////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////
////////////                       GrROOT
////////////
////////////          Purpose:
////////////                   To assist in the analysis of data from
////////////                 the gretina/S800 experimental setup.
////////////                          
////////////          Current Maintainers:
////////////                 Kathrin Wimmer  (wimmer@phys.s.u-tokyo.ac.jp)
////////////                 Eric Lunderberg (lunderberg@nscl.msu.edu)
////////////
////////////          Distribution:
////////////                   Please do not redistribute this software directly.
////////////                   If someone new wants a copy of this software,
////////////                 email one of the maintainers for the download link.
////////////                   This allows us to keep track of who has the software,
////////////                 and properly distribute updates and bug fixes.
////////////                 
////////////          Suggestions:
////////////                   We view the development of the software as a collaborative
////////////                 effort, and as such, welcome and appreciate any suggestions
////////////                 for bug fixes and improvements.
////////////
////////////          Disclaimer:
////////////                 This software is provided as-is, with no warranty.
////////////                 No current or future support is guaranteed for this software.
////////////
////////////
////////////          This code is modefitied by GLZ 12/19/2024 
////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
#include <iostream>
#include <iomanip>
#include <string.h>
#include <sys/time.h>

#include "TFile.h"
#include "TTree.h"
#include "TChain.h"
#include "TH1F.h"
#include "TH2F.h"
#include "TH2S.h"
#include "TH1S.h"
#include "TProfile.h"
#include "TCanvas.h"
#include "TPad.h"
#include "TStyle.h"
#include "TROOT.h"
#include "TMath.h"
#include "TCutG.h"
#include "TEnv.h"
#include "TKey.h"
#include "TDirectory.h"

#include "CommandLineInterface.hh"
#include "S800Calc.hh"
#include "GretinaCalc.hh"
#include "Mode3Calc.hh"
#include "Scaler.hh"
#include "CalHistograms.hh"
using namespace TMath;
using namespace std;

//not nice but works at least
static TCutG* TimeCut;
static bool foundTCut = false;

// adding bool for bta_ata cut -RS (06.07.2023)
// creating vector to hold bta(Y)_vs_ata(X) cuts - RS (06.07.2023)
static vector<TCutG*> scattering_angle_cuts;
static bool found_scattering_angle_cut = false;

//RE New in v4.1_LT -> Making function to return the cylindrical rho distance from the beam axis.
double CalHistograms::rho(TVector3 hit){
  return sqrt(hit.X()*hit.X()+hit.Y()*hit.Y());
}

//RE New in v4.1_LT -> Take the positions of the compton scatter interaction and the next interaction (either compt or photoelec) and the position
//of the decay.  calculate and return the angle between the incoming and outgoing compton scatter gammas.
double CalHistograms::CasZangle(TVector3 posCompt, TVector3 posNext,const TVector3& decay){
  posCompt-=decay;
  posNext-=decay;
  double casZangle = posCompt.Angle(posNext-posCompt);
  return casZangle;
}

//RE New in v4.1_LT
//This function is based on the Compton scatter formula. It takes the energy deposited "enDep" and the energy remaining "enRem" after a Compton scatter event and returns "Cos(theta)"
//The "Cos(theta)" from this function is based only on the energy information. It was compared with the angle determined only from gamma-ray position information to judge whether the gamma ray hits were properly reconstructed
double CosComptAngle(double enDep,double enRem){
  double cosAngle = 1-511.0/enRem+511.0/(enDep+enRem);
  return cosAngle;
}

//RE New in v4.1_LT
//This is the function that determines the decay position. It takes an observed gamma ray "gammaKnown", the expected ion-frame energy "eTrueGammaKnown", and the velocity of the ion "beta".
//It returns a vector corresponding to the position of the decay relative to the target
TVector3 CalHistograms::CascadeZdecay(HitCalc* gammaKnown, double eTrueGammaKnown, double beta){
  TVector3 decay(0.,0.,-10.);
  
  double relGamma = 1/sqrt(1-beta*beta);
  
  double eLabGammaKnown = gammaKnown->GetEnergy();

  TVector3 hitGammaKnown = gammaKnown->GetPosition();
  double zHitGammaKnown = hitGammaKnown.Z();
  double xHitGammaKnown = hitGammaKnown.X();
  double yHitGammaKnown = hitGammaKnown.Y();

  double thetaGammaKnown = acos((1-(eTrueGammaKnown)/(relGamma*eLabGammaKnown))/beta);
  double rhoHitGammaKnown = sqrt(xHitGammaKnown*xHitGammaKnown+yHitGammaKnown*yHitGammaKnown);

  double dDecayToHit;     //this is the distance along the z-axis from the decay to the gamma hit.  positive is downstream/  
  if(thetaGammaKnown==Pi()/2.){  //RE New in v4.1_LT -> Including ways to handle the error cases.  
    dDecayToHit = 0.;
  }
  else if(thetaGammaKnown==0){  //gamma was emitted straight ahead.  impossible to detect both ion and gamma
    return decay;                  //for this case in our geometry.  
  }                              
  else if(thetaGammaKnown==Pi()){  //gamma was emitted straight backward.  impossible to detect both ion and gamma
    return decay;                  //for this case in our geometry.  
  }
  else{
    dDecayToHit = rhoHitGammaKnown/tan(thetaGammaKnown);
  }
  
  decay.SetZ(zHitGammaKnown - dDecayToHit);
  
  return decay;
}

//RE New in v4.1_LT
//This function performs the Doppler-shift correction using the decay position from the CascadeZdecay function. It takes the other observed gamma ray "gammaOfInterest", the decay position "decay", and the velocity "beta".
//It returns the Doppler-shift corrected energy
double CalHistograms::CascadeCorrectedE(HitCalc* gammaOfInterest, const TVector3& decay, double beta){
  double relGamma = 1/sqrt(1-beta*beta);

  double eLabGammaOfInterest = gammaOfInterest->GetEnergy();
  TVector3 hitGammaOfInterest = gammaOfInterest->GetPosition();
  double zHitGammaOfInterest = hitGammaOfInterest.Z();
  double xHitGammaOfInterest = hitGammaOfInterest.X();
  double yHitGammaOfInterest = hitGammaOfInterest.Y();

  double rhoHitGammaOfInterest = sqrt(xHitGammaOfInterest*xHitGammaOfInterest+yHitGammaOfInterest*yHitGammaOfInterest);
  double dDecayToHit = zHitGammaOfInterest - decay.Z();
  
  double thetaGammaOfInterest = atan(rhoHitGammaOfInterest/dDecayToHit);

  if(thetaGammaOfInterest<0.){
    thetaGammaOfInterest = thetaGammaOfInterest+Pi();
  }
  else{   //theta is in the good range.  do nothing.  
    ;
  }
  
  double eCorrGammaOfInterest = eLabGammaOfInterest*relGamma*(1-beta*cos(thetaGammaOfInterest));
  
  return eCorrGammaOfInterest;
}

//RE New in v4.1_LT
//Function used for some gates. For one gamma ray, it calculates the distance from the first hit position to the furthest hit position. In the code I call this quantity the "span" but it also makes sense to call it the "maximum radius" of collection of hit positions for one gamma ray
double CalHistograms::CalcSpan(HitCalc* gamma){
  double span;
  
  if(gamma->GetIPMult()==1){
    span = 0.0;
  }
  else if(gamma->GetIPMult()>1){
    double maxDist = 0.0;
    int maxIndex = 0;
    for(int i=0;i<gamma->GetIPMult();i++){
      double thisDist = (gamma->GetIPoints()[i]->GetPosition()-gamma->GetPosition()).Mag();
      if(thisDist>maxDist){
	maxDist=thisDist;
	maxIndex=i;
      }
    }
    span=maxDist;
  }
  else{
    //ip mult is negative for some reason - error.
    span = -1.0;
  }
  //  cout << "span: " << span << endl << endl;
  return span;
}

void CalHistograms::FillHistograms(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c){

  //bool hass800 = s800->GetTimeS800()!=0;
  bool hasgret = gr->GetMult()>0;

  //Declare the histograms here.
  static vector<TCutG*> InPartCut;
  static vector<vector<TCutG*> > OutPartCut;

  static PAD* pad[2];
  static PPAC* ppac[2];
  static IC* ich;
  static STACKPIN* stackpin; //AR New in v4.1_LT
  static SCINT* scint;
  static TOF* tof;
  static TRACK* track;
  static IITRACK* iitrack;
  static HODO* hodo;

  static bool foundCuts = false;
  static bool NoInCuts = false;
  if (!foundCuts){
    //Read in the cuts file for incoming and outgoing particle ID
    if(fhasfile){
      cout << "Cuts were created for ";
      if (ftac&(1<<2))
	cout << "MTDC";
      else if (ftac&(1<<0))
	cout << "TDC";
      else
	cout << "TAC";
      cout << " data and are applied to the ";
      if (ftac&(1<<1))
	cout << "XFP";
      else
	cout << "OBJ";
      cout << " scintillator" << endl;


      //Remember the current directory so that we can revert to it later.
      TDirectory* outfile = gDirectory;

      char* Name = NULL;
      char* Name2 = NULL;
      TFile *cFile = new TFile(fcutfile);
      TIter next(cFile->GetListOfKeys());
      TKey *key;
      while((key=(TKey*)next())){
	if(strcmp(key->GetClassName(),"TCutG") == 0){
	  Name = (char*)key->GetName();
	  if(strstr(Name,"in") && !strstr(Name,"out")){
	    cout << "incoming cut found "<<Name << endl;
	    InPartCut.push_back((TCutG*)cFile->Get(Name));
	  }
	  if(strstr(Name,"tgam")){
	    cout << "timing cut found "<<Name << endl;
	    TimeCut = (TCutG*)cFile->Get(Name);
	    foundTCut = true;
	  }
    		  if(strstr(Name,"scatter")){
			
			// If the scattering angle cut hasn't been set to true yet
			if(!found_scattering_angle_cut)
				found_scattering_angle_cut=true;
			
			cout<<"Scattering Angle Cut Found: "<< Name<<endl;
			scattering_angle_cuts.push_back((TCutG*)cFile->Get(Name));
			//found_bfpafp_cut=true;

		  }
    }
  }
      TIter next2(cFile->GetListOfKeys());
      if(InPartCut.size()>0){
	OutPartCut.resize(InPartCut.size());
	while((key=(TKey*)next2())){
	  if(strcmp(key->GetClassName(),"TCutG") == 0){
	    Name = (char*)key->GetName();
	    if(strstr(Name,"in") && strstr(Name,"out")){
	      for(unsigned short i=0;i<InPartCut.size();i++){
		Name2 = (char*)InPartCut[i]->GetName();
		if(strstr(Name,strstr(Name2,Name2))){
		  OutPartCut[i].push_back((TCutG*)cFile->Get(Name));
		  cout << "outgoing cut found "<<Name << endl;
		}
	      }
	    }
	  }
	}
      }
      else{
	OutPartCut.resize(1);
	while((key=(TKey*)next2())){
	  if(strcmp(key->GetClassName(),"TCutG") == 0){
	    Name = (char*)key->GetName();
	    if(!strstr(Name,"in") && strstr(Name,"out")){
	      OutPartCut[0].push_back((TCutG*)cFile->Get(Name));
	      cout << "outgoing cut found (no incoming!) "<<Name << endl;
	      NoInCuts = true;
	    }
	  }
	}
      }
      cFile->Close();
      outfile->cd();

      foundCuts = true;
      cout << "Cuts found" << endl;
    }
  }

  //-------------------------------------------------------------------------
  //*************************************************************************
  //Fill the histograms here.
  //*************************************************************************
  //-------------------------------------------------------------------------

  int hp = s800->GetRegistr();
  FillI("registr",20,0,20,hp);
  for(int j=0;j<16;j++){
    if(hp & (1<<j))
      FillI("trigbit",16,0,16,j);
  }

  stackpin = s800->GetSTACKPIN(); //AR New in v4.1_LT
  ich = s800->GetIC();
  tof = s800->GetTOF();
  track = s800->GetTRACK();
  iitrack = s800->GetIITRACK();
  hodo = s800->GetHODO();
  for(UShort_t p=0; p<2;p++){
    pad[p] = s800->GetPAD(p);
    ppac[p] = s800->GetPPAC(p);
  }

  FillHistogramsNoGate(gr,s800,m3c);
  FillHistogramsGateIn(gr,s800,m3c,"all");
  FillHistogramsGateOut(gr,s800,m3c,"all");
  for(UShort_t in=0;in<InPartCut.size();in++){ // loop over incoming cuts
    if( (ftac==1 && InPartCut[in]->IsInside(tof->GetOBJ(),tof->GetXFP()))
	|| (ftac==3 && InPartCut[in]->IsInside(tof->GetOBJ(),tof->GetXFP())) 
	|| (ftac==0 && InPartCut[in]->IsInside(tof->GetTACOBJ(),tof->GetTACXFP())) 
	|| (ftac==2 && InPartCut[in]->IsInside(tof->GetTACOBJ(),tof->GetTACXFP())) 
	|| (ftac==5 && InPartCut[in]->IsInside(tof->GetMOBJ(),tof->GetMXFP()))
	|| (ftac==6 && InPartCut[in]->IsInside(tof->GetMOBJ(),tof->GetMXFP())) ){
      const char* inname = InPartCut[in]->GetName();
      FillHistogramsGateIn(gr,s800,m3c,inname);
      if(hasgret){
	FillHistogramsGateIn(gr,s800,m3c,Form("%s_coinc",inname));
      }
      FillHistogramsGateOut(gr,s800,m3c,inname);
      
      for(UShort_t ou=0;ou<OutPartCut[in].size();ou++){ // loop over PID cuts
	if((ftac == 1 && OutPartCut[in][ou]->IsInside(tof->GetOBJC(),ich->GetDE()))
	   ||(ftac == 0 && OutPartCut[in][ou]->IsInside(tof->GetTACOBJC(),ich->GetDE()))
	   ||(ftac == 3 && OutPartCut[in][ou]->IsInside(tof->GetXFPC(),ich->GetDE()))
	   ||(ftac == 2 && OutPartCut[in][ou]->IsInside(tof->GetTACXFPC(),ich->GetDE()))
	   ||(ftac == 5 && OutPartCut[in][ou]->IsInside(tof->GetMOBJC(),ich->GetDE()))
	   ||(ftac == 6 && OutPartCut[in][ou]->IsInside(tof->GetMXFPC(),ich->GetDE()))){
	  const char* outname = OutPartCut[in][ou]->GetName();

	  FillHistogramsGateOut(gr,s800,m3c,outname);
	  Fill(Form("txfp_%s",outname), 600,-300,300,track->GetXFP());
//	  if (hasgret){
//	    FillHistogramsGateOut(gr,s800,m3c,Form("%s_coinc",outname));
//	  }

	}

      }
    }
  }
  if(NoInCuts){
    // for pure beams, i.e. no incoming cut required or possible
    for(UShort_t ou=0;ou<OutPartCut[0].size();ou++){ // loop over PID cuts
      if((ftac == 1 && OutPartCut[0][ou]->IsInside(tof->GetOBJC(),ich->GetDE()))
	 ||(ftac == 0 && OutPartCut[0][ou]->IsInside(tof->GetTACOBJC(),ich->GetDE()))
	 ||(ftac == 3 && OutPartCut[0][ou]->IsInside(tof->GetXFPC(),ich->GetDE()))
	 ||(ftac == 2 && OutPartCut[0][ou]->IsInside(tof->GetTACXFPC(),ich->GetDE()))
	 ||(ftac == 5 && OutPartCut[0][ou]->IsInside(tof->GetMOBJC(),ich->GetDE()))
	 ||(ftac == 6 && OutPartCut[0][ou]->IsInside(tof->GetMXFPC(),ich->GetDE()))){
	const char* outname = OutPartCut[0][ou]->GetName();

	FillHistogramsGateOnlyOut(gr,s800,m3c,outname);

      }
    }
  }

}
void CalHistograms::FillHistogramsNoGate(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c){

  PAD* pad[2];
  PPAC* ppac[2];
  for(UShort_t p=0; p<2;p++){
    pad[p] = s800->GetPAD(p);
    ppac[p] = s800->GetPPAC(p);
  }
  IC* ich = s800->GetIC();
  STACKPIN* stackpin = s800->GetSTACKPIN(); //AR New in v4.1_TL
  MTDC* mtdc = s800->GetMTDC(); //AR New in v4.1_TL
  TOF* tof = s800->GetTOF();
  TRACK* track = s800->GetTRACK();
  IITRACK* iitrack = s800->GetIITRACK();
  HODO* hodo = s800->GetHODO();
  bool hasgret = gr->GetMult()>0;



  Double_t sum =0;
  for(UShort_t c=0; c<hodo->GetEnergy()->size();c++){
    Short_t ch = hodo->GetChannel()->at(c);
    Fill(Form("hodo_%d",ch),1000,0,4000,hodo->GetEnergy()->at(c));
    Fill("hodo_vs_ch",32,0,32,ch,1000,0,4000,hodo->GetEnergy()->at(c));
    Fill("hodo_all",1000,0,4000,hodo->GetEnergy()->at(c));
    Fill(Form("hodotime_%d",ch),1000,0,4000,hodo->GetTime());
    Fill("hodotime_vs_ch",32,0,32,ch,1000,0,4000,hodo->GetTime());
    Fill("hodotime_all",1000,0,4000,hodo->GetTime());
  

    if(hodo->GetEnergy()->at(c)>50)
      sum+=hodo->GetEnergy()->at(c);
  }// hodo energy
  Fill("hodo_sum",1000,0,4000,sum);




  for(UShort_t i=0;i<tof->GetMOBJV()->size();i++){
    for(UShort_t j=0;j<tof->GetMXFPV()->size();j++){
      Fill("xfp_vs_objm",
	   fmobj_range[0],fmobj_range[1],fmobj_range[2],tof->GetMOBJV()->at(i),
	   fmxfp_range[0],fmxfp_range[1],fmxfp_range[2],tof->GetMXFPV()->at(j));
    }
  }
  for(UShort_t i=0;i<tof->GetMOBJCV()->size();i++){
    for(UShort_t j=0;j<tof->GetMXFPCV()->size();j++){
      Fill("xfpc_vs_objmc",
	   fmobj_range[0],fmobj_range[1],fmobj_range[2],tof->GetMOBJCV()->at(i),
	   fmxfp_range[0],fmxfp_range[1],fmxfp_range[2],tof->GetMXFPCV()->at(j));
    }
  }
  

  for (UShort_t g = 0; g < gr->GetMult(); g++)
  {
	  HitCalc *hit = gr->GetHit(g);
	  float energy = hit->GetEnergy();
	  float energy_dc = hit->GetDCEnergy();
	  TVector3 pos = hit->GetPosition(); // AR New in v4.1_TL
	
	  Fill("egam",4000, 0, 4000, energy);
	  Fill("egamdc",4000, 0, 4000, energy_dc);
	  Fill("egamdc_tgam",4000, 0, 4000, energy_dc,400, -200, 200, hit->GetTime());
    Fill("egam_tgam",4000, 0, 4000, energy,400, -200, 200, hit->GetTime());

	  }
	  for (UShort_t g = 0; g < gr->GetMultAB(); g++)
	  {
		  HitCalc *hit = gr->GetHitAB(g);
		  float energy = hit->GetEnergy();
		  float energy_dc = hit->GetDCEnergy();

		  Fill("egamAB",4000, 0, 4000, energy);
		  Fill("egamAB_tgam",4000, 0, 4000, energy,400, -200, 200, hit->GetTime());
		  Fill("egamABdc",4000, 0, 4000, energy_dc);
		  Fill("egamABdc_tgam",4000, 0, 4000, energy_dc,400, -200, 200, hit->GetTime());



	  }
  }

void CalHistograms::FillHistogramsGateIn(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c, const char* inname){
  PAD* pad[2];
  PPAC* ppac[2];
  for(UShort_t p=0; p<2;p++){
    pad[p] = s800->GetPAD(p);
    ppac[p] = s800->GetPPAC(p);
  }
  IC* ich = s800->GetIC();
  TOF* tof = s800->GetTOF();
  TRACK* track = s800->GetTRACK();
  IITRACK* iitrack = s800->GetIITRACK();
  HODO* hodo = s800->GetHODO();
  bool hasgret = gr->GetMult()>0;
  STACKPIN* stackpin = s800->GetSTACKPIN(); //AR New in v4.1_TL
  MTDC* mtdc = s800->GetMTDC(); //AR New in v4.1_TL




  Fill(Form("Y_val_CRDC0_%s",inname), 4000,-2000,2000,s800->GetPAD(0)->GetY()); 
  Fill(Form("Y_val_CRDC1_%s",inname), 4000,-2000,2000,s800->GetPAD(1)->GetY()); 

  // Adding histograms to see the X position in CRDC0 and CRDC1 - RS (10.18.2022)
  Fill(Form("X_val_CRDC0_%s",inname), 4000,-2000,2000,s800->GetPAD(0)->GetX()); 
  Fill(Form("X_val_CRDC1_%s",inname), 4000,-2000,2000,s800->GetPAD(1)->GetX()); 
  

  


  Double_t sum =0;
  for(UShort_t c=0; c<hodo->GetEnergy()->size();c++){
    if(hodo->GetEnergy()->at(c)>50)
      sum+=hodo->GetEnergy()->at(c);
  }//hodo energy
  Fill(Form("hodo_sum_%s",inname),1000,0,4000,sum);
 

  

  for(UShort_t i=0;i<tof->GetMOBJV()->size();i++){
    for(UShort_t j=0;j<tof->GetMXFPV()->size();j++){
      Fill(Form("xfp_vs_objm_%s",inname),
	   fmobj_range[0],fmobj_range[1],fmobj_range[2],tof->GetMOBJV()->at(i),
	   fmxfp_range[0],fmxfp_range[1],fmxfp_range[2],tof->GetMXFPV()->at(j));
    }
  }

    for(UShort_t i=0;i<tof->GetMOBJCV()->size();i++){
    for(UShort_t j=0;j<tof->GetMXFPCV()->size();j++){
     Fill(Form("xfpC_vs_objmC_%s",inname),
	   fmobj_range[0],fmobj_range[1],fmobj_range[2],tof->GetMOBJCV()->at(i),
	   fmxfp_range[0],fmxfp_range[1],fmxfp_range[2],tof->GetMXFPCV()->at(j));
    }
  }

  
}


void CalHistograms::FillHistogramsGateOut(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c, const char* outname){
  TString oname = outname;

  PAD* pad[2];
  PPAC* ppac[2];
  for(UShort_t p=0; p<2;p++){
    pad[p] = s800->GetPAD(p);
    ppac[p] = s800->GetPPAC(p);
  }
  IC* ich = s800->GetIC();
  TOF* tof = s800->GetTOF();
  TRACK* track = s800->GetTRACK();
  IITRACK* iitrack = s800->GetIITRACK();
  HODO* hodo = s800->GetHODO();
  bool hasgret = gr->GetMult()>0;

//This is for crcd offsets
  	// Adding the CRDCY positions for the outgoing cuts - RS (10.25.2022)
	Fill(Form("Y_val_CRDC0_%s",oname.Data()), 4000,-2000,2000,s800->GetPAD(0)->GetY()); 
	Fill(Form("Y_val_CRDC1_%s",oname.Data()), 4000,-2000,2000,s800->GetPAD(1)->GetY()); 

	// Adding histograms to see the X position in CRDC0 and CRDC1 - RS (10.18.2022)
	Fill(Form("X_val_CRDC0_%s",oname.Data()), 4000,-2000,2000,s800->GetPAD(0)->GetX()); 
	Fill(Form("X_val_CRDC1_%s",oname.Data()), 4000,-2000,2000,s800->GetPAD(1)->GetX());

  Fill(Form("ICde_vs_objmc_%s",oname.Data()),1300,-4000,-3300,tof->GetMOBJC(),4000,0,4000,ich->GetDE());

  Double_t sum =0;
  for(UShort_t c=0; c<hodo->GetEnergy()->size();c++){
    Short_t ch = hodo->GetChannel()->at(c);
     Fill(Form("hodo_ch%d_%s",ch,oname.Data()),1000,0,4000,hodo->GetEnergy()->at(c));
     Fill(Form("hodo_vs_ch_%s",oname.Data()),32,0,32,ch,1000,0,4000,hodo->GetEnergy()->at(c));
     Fill(Form("hodo_all_%s",oname.Data()),1000,0,4000,hodo->GetEnergy()->at(c));
     Fill(Form("hodotime_ch%d_%s",ch,oname.Data()),1000,0,4000,hodo->GetTime());
     Fill(Form("hodotime_vs_ch_%s",oname.Data()),32,0,32,ch,1000,0,4000,hodo->GetTime());
     //Fill(Form("hodotime_all_%s",oname.Data()),1000,0,4000,hodo->GetTime());

    Fill(Form("hodotime_all_%s",oname.Data()),3000,0,3000,hodo->GetTime());
    Fill(Form("hodotime_vs_energy_%s",oname.Data()),1000,0,2000,hodo->GetEnergy()->at(c),3000,0,3000,hodo->GetTime());



  if(hodo->GetEnergy()->at(c)>50)
      sum+=hodo->GetEnergy()->at(c);
  }// hodo energy
  if(sum>0.){
  Fill(Form("hodo_sum_%s",oname.Data()),1000,0,2000,sum);
  }
  
  //having an energy gate in no dc energy 
for (UShort_t g=0; g<gr->GetMult(); g++){
    HitCalc* hit = gr->GetHit(g);
    float energy = hit->GetEnergy();
    float energy_dc = hit->GetDCEnergy();
    TVector3 pos = hit->GetPosition();//AR New in v4.1_TL

float dphi = hit->GetPosition().Phi() - track->GetPhi();
 while(dphi<0)
 dphi+=2*TMath::Pi();
 	while(dphi>2*TMath::Pi())
 dphi-=2*TMath::Pi();

float dtheta = hit->GetPosition().Theta() - track->GetTheta();
 while(dtheta<0)
 dtheta+=2*TMath::Pi();
    while(dtheta>2*TMath::Pi())
 dtheta-=2*TMath::Pi();

  }
 

  for (UShort_t g=0; g<gr->GetMult(); g++){
	
	  HitCalc *hit = gr->GetHit(g);

	  float energy = hit->GetEnergy();
	  float energy_dc = hit->GetDCEnergy();
	  TVector3 pos = hit->GetPosition(); // AR New in v4.1_TL
	  int CrysID = hit->GetCrystal();


	 if(energy >250.0){
		  Fill(Form("Mult"), 100, 0, 100, gr->GetMult());
	  }
    //Fill(Form("Gretphi_grettheta%s", oname.Data()), 400,-4.0,4.0, hit->GetPosition().Phi(), 180, 0, 3.14159, hit->GetPosition().Theta());

	  Fill(Form("egam_%s", oname.Data()),4000, 0, 4000, energy);
	  Fill(Form("egamdc_%s",oname.Data()),4000,0,4000,energy_dc);		   
	  Fill(Form("egam_tgam_%s", oname.Data()),4000, 0, 4000, energy,400, -200, 200, hit->GetTime());
	  Fill(Form("egamdc_tgam_%s", oname.Data()),4000, 0, 4000, energy_dc,400, -200, 200, hit->GetTime());
    Fill(Form("egamdc_grettheta_%s",oname.Data()),4000,0,4000,energy_dc,180,0,3.14159,hit->GetPosition().Theta());
	  Fill(Form("egam_grettheta_%s",oname.Data()),4000,0,4000,energy,180,0,3.14159,hit->GetPosition().Theta());	


  if(foundTCut && TimeCut->IsInside(energy,hit->GetTime())){
	  Fill(Form("egam_grettheta_%s_tcut",oname.Data()),4000,0,4000,energy,180,0,3.14159,hit->GetPosition().Theta());	
		Fill(Form("egam_%s_tcut",oname.Data()),4000,0,4000,energy);
		Fill(Form("egamdc_%s_tcut",oname.Data()),4000,0,4000,energy_dc);
		Fill(Form("egamdc_grettheta_%s_tcut",oname.Data()),4000,0,4000,energy_dc,180,0,3.14159,hit->GetPosition().Theta());	
		Fill(Form("depth_grettheta_%s_tcut",oname.Data()),180,0,3.14159,hit->GetPosition().Theta(),2000,-15,185,hit->GetDepth());



	}


	

  }

  for(UShort_t g=0;g<gr->GetMultAB();g++){
    HitCalc* hit = gr->GetHitAB(g);
    float energy = hit->GetEnergy();
    float energy_dc = hit->GetDCEnergy();
    Fill(Form("egamAB_%s",oname.Data()),4000,0,4000,energy);
    Fill(Form("egamABdc_%s",oname.Data()),4000,0,4000,energy_dc);
    Fill(Form("egamABdc_tgam_%s",oname.Data()),4000,0,4000,energy_dc,400,-200,200,hit->GetTime());
    Fill(Form("egamABdc_grettheta_%s",oname.Data()),4000,0,4000,energy_dc,180,0,3.14159,hit->GetPosition().Theta());


/*if (hit->GetTime() >= 20 && hit->GetTime() <= 26) {*/
	if(foundTCut && TimeCut->IsInside(energy,hit->GetTime())){
      
      Fill(Form("egamAB_%s_tcut",oname.Data()),4000,0,4000,energy);
      Fill(Form("egamABdc_%s_tcut",oname.Data()),4000,0,4000,energy_dc);
      Fill(Form("egamAB_grettheta_%s_tcut",oname.Data()),4000,0,4000,energy,180,0,3.14159,hit->GetPosition().Theta());
      Fill(Form("egamABdc_grettheta_%s_tcut",oname.Data()),4000,0,4000,energy_dc,180,0,3.14159,hit->GetPosition().Theta());

      if (g == 0 && gr->GetMult() == 1){
		  Fill(Form("egamAB_grettheta_%s_tcut_Mult1"),4000, 0, 4000, energy,180,0,3.14159,hit->GetPosition().Theta());
      Fill(Form("egamABdc_grettheta_%s_tcut_Mult1"),4000, 0, 4000, energy_dc,180,0,3.14159,hit->GetPosition().Theta());
	  }


if(found_scattering_angle_cut){

			char buffer[256];
			const char* extra = "_";

			vector<TCutG*> reorg_scatt_cuts;
			
			// manually organize the cuts in the right order
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(3)); //0.5
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(4)); //1.0
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(5)); //1.5
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(0)); //2.0
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(1)); //2.5
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(2)); //3.0
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(6)); //3.5
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(7)); //4.0
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(8)); //4.5
			reorg_scatt_cuts.push_back(scattering_angle_cuts.at(9)); //5.0


			for(UShort_t deg_cut = 0;deg_cut<reorg_scatt_cuts.size()-1;deg_cut++){

				const char *degcut_name = reorg_scatt_cuts.at(deg_cut)->GetName();
				const char *degcut_name2 = reorg_scatt_cuts.at(deg_cut+1)->GetName();

				// Combine the names of the cuts
				strncpy(buffer,oname.Data(),sizeof(buffer)); //inBeamoutBeam
				strncat(buffer,extra,sizeof(buffer));// _ 
				strncat(buffer,degcut_name,sizeof(buffer)); // scatter_deg#
				strncat(buffer,extra,sizeof(buffer));// _ 
				strncat(buffer,degcut_name2,sizeof(buffer)); // scatter_deg#


				// Checking if it is within the ring I am specifying
				if( !(reorg_scatt_cuts.at(deg_cut)->IsInside(track->GetATA(),track->GetBTA())) && reorg_scatt_cuts.at(deg_cut +1 )->IsInside(track->GetATA(),track->GetBTA()) ){

					Fill(Form("atabta_%s",buffer),
						200,-100,100,track->GetATA(),
						200,-100,100,track->GetBTA());

					Fill(Form("xfpafp_%s_tcut",buffer),
						600,-300,300,track->GetAFP(),
						200,-100,100,track->GetXFP());
					// Create angular acceptance that is gated on time, scattering angle, and isotope
					/*Fill(Form("afpxfp_%s_tcut",buffer),
						600,-300,300,track->GetXFP(),
						200,-100,100,track->GetAFP());*/
				}
			}


			// Loop through all of the scattering angle cuts that are in the cut file
			for(UShort_t deg_cut = 0;deg_cut<scattering_angle_cuts.size();deg_cut++){
				

				const char *degcut_name = scattering_angle_cuts.at(deg_cut)->GetName();

				// Combine the names of the cuts
				strncpy(buffer,oname.Data(),sizeof(buffer)); //inBeamoutBeam
				strncat(buffer,extra,sizeof(buffer));// _ 
				strncat(buffer,degcut_name,sizeof(buffer)); // scatter_deg#

				// Check to see if the hit in this event is within the cut
				// if(scattering_angle_cuts.at(deg_cut)->IsInside(track->GetAFP(),track->GetBFP())){
				// ATA on x-axis, BTA on y-axis
				if(scattering_angle_cuts.at(deg_cut)->IsInside(track->GetATA(),track->GetBTA())){
					Fill(Form("egamABdc_scattering_angle_cuts_%s_tcut",buffer),
						4000,0,4000,energy_dc);

					Fill(Form("egamAB_scattering_angle_cuts_%s_tcut",buffer),
						4000,0,4000,energy);
					Fill(Form("egamABdc_grettheta_scattering_angle_cuts%s_tcut",buffer),
						4000,0,4000,energy_dc,
						180,0,3.14159,hit->GetPosition().Theta());

					Fill(Form("egamAB_grettheta_scattering_angle_cuts%s_tcut",buffer),
						4000,0,4000,energy,
						180,0,3.14159,hit->GetPosition().Theta());
					Fill(Form("afpbfp_%s",buffer),
						200,-100,100,track->GetAFP(),
						200,-100,100,track->GetBFP());

					Fill(Form("atabta_%s",buffer),
						200,-100,100,track->GetATA(),
						200,-100,100,track->GetBTA());

					Fill(Form("scatter_%s_tcut",buffer),
	   				500,0,0.5,track->GetTheta());

					// Create angular acceptance that is gated on time, scattering angle, and isotope
					Fill(Form("afpxfp_%s_tcut",buffer),
						600,-300,300,track->GetXFP(),
						200,-100,100,track->GetAFP());

				} // end of if-statement checkinf if gammas are in the gate
				
				// Clear the character buffer
				buffer[0] = '\0';

			} // end of for-loop over scattering angle gates
		}

      
   }


  }


  int hp = s800->GetRegistr();
  Fill(Form("registr_%s",oname.Data()),
       20,-0.5,19.5,hp);
  for(int j=0;j<16;j++){
    if(hp & (1<<j)){
      Fill(Form("trigbit_%s",oname.Data()),
	   16,-0.5,15.5,j);
    }
  }

  if(fCal&(1<<2)){


    Fill(Form("afp_vs_objm_%s",oname.Data()),
	 fmobj_range[0],fmobj_range[1],fmobj_range[2],tof->GetMOBJ(),
	 100/2,-100,100,track->GetAFP());

    Fill(Form("afp_vs_objmC_%s",oname.Data()),
	 fmobjC_range[0],fmobjC_range[1],fmobjC_range[2],tof->GetMOBJC(),
	 100/2,-100,100,track->GetAFP());

  }



  

}
void CalHistograms::FillHistogramsGateOnlyOut(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c, const char* outname){
  //in case you have pure beam, fill here
}

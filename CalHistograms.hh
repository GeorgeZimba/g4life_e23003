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
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////
#ifndef CAL_HISTOGRAMS_HH__
#define CAL_HISTOGRAMS_HH__

#include <iostream>
#include <iomanip>

#include "TObject.h"
#include "TFile.h"
#include "TTree.h"
#include "TList.h"
#include "TH1.h"
#include "TH2.h"
#include "TH3.h"
#include "TEnv.h"
#include "math.h"
#include <iostream>
#include <iomanip>
#include <fstream>
#include <string>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdexcept>

#include "Settings.hh"

using namespace std;

#define CUTFILE_NAMELENGTH 100

class GretinaCalc;
class S800Calc;
class Mode3Calc;

class CalHistograms {
public:
  CalHistograms(Settings* set = NULL,int tac=0, int cal = 0, int upstream = 0, char* cutfile=NULL, int nentries=100000){
    Init(set,tac,cal,upstream,cutfile,nentries);
  }
  ~CalHistograms(){
    delete fhlist;
  }
  void Init(Settings* set,int tac, int cal,int upstream, char* cutfile,int nentries){
    if (set!=NULL){
      fSett = set;
    } else {
      fSett = new Settings;
    }
    fCal = cal;
    //RE New in v4.1_LT -> The new parameter fUpstream is set to be the value passed upon initialization from Cal_histos.cc
    fUpstream = upstream;
    fhlist = new TList;
    fnentries = nentries;
    if(tac > -1 && tac < 6 && tac!=4){
      ftac = tac;
    } else {
      cout << "Unknown timing number: " << tac << endl;
      cout << "Please use 0 for TAC timing or 1 for TDC timing  or 5 for MTDC timing if you want to use the OBJ scintillator" << endl;
      cout << "Please use 2 for TAC timing or 3 for TDC timing  or 6 for MTDC timing if you want to use the XFP scintillator" << endl;
      cout << "Assuming that the cuts were made for TAC timing and the OBJ scintillator" << endl;
      ftac = 0;
    }
    if(cutfile!=NULL){
      cout << "using cutfile " << cutfile << endl;
      if(strlen(cutfile)<CUTFILE_NAMELENGTH-1){
	strcpy(fcutfile,cutfile);
	fhasfile = true;
      } else {
	cout << "cutfile filename too long" << endl;
	cout << "please increase CUTFILE_NAMELENGTH in CalHistograms.hh" << endl;
	fhasfile = false;
      }
    } else {
      fhasfile = false;
    }
    fentry =0;

    for(int i=0;i<3;i++){
      fstackpin_range[i] = fSett->GetRangeSTACKPIN(i); //AR New in v4.1_TL 
      fobj_range[i] = fSett->GetRangeOBJ(i);
      fxfp_range[i] = fSett->GetRangeXFP(i);
      ftacobj_range[i] = fSett->GetRangeTACOBJ(i);
      ftacxfp_range[i] = fSett->GetRangeTACXFP(i);
      fmobj_range[i] = fSett->GetRangeMOBJ(i);
      fmxfp_range[i] = fSett->GetRangeMXFP(i);
      fIC_range[i] = fSett->GetRangeIC(i);
      fobjC_range[i] = fSett->GetRangeOBJC(i);
      fxfpC_range[i] = fSett->GetRangeXFPC(i);
      ftacobjC_range[i] = fSett->GetRangeTACOBJC(i);
      ftacxfpC_range[i] = fSett->GetRangeTACXFPC(i);
      fmobjC_range[i] = fSett->GetRangeMOBJC(i);
      fmxfpC_range[i] = fSett->GetRangeMXFPC(i);
      fPP_range[i] = fSett->GetRangePP(i);
    }

  }
  void AddEntry(){
    fentry++;
  }
  TList* GetHList(){return fhlist;}
  void Write(){
    fhlist->Sort();
    fhlist->Write();
  }

  void FillHistograms(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c);

  void FillI(string name,int bins, double low, double high, double value){
    try{
      fhmap1d.at(name)->Fill(value);
    } catch(out_of_range e) {
      TH1I* newHist = new TH1I(name.c_str(),name.c_str(),bins,low,high);
      newHist->Fill(value);
      fhlist->Add(newHist);
      fhmap1d[name] = newHist;
    }
  }
  void FillS(string name,int bins, double low, double high, double value){
    try{
      fhmap1d.at(name)->Fill(value);
    } catch(out_of_range e) {
      TH1S* newHist = new TH1S(name.c_str(),name.c_str(),bins,low,high);
      newHist->Fill(value);
      fhlist->Add(newHist);
      fhmap1d[name] = newHist;
    }
  }
  void Fill(string name,int bins, double low, double high, double value, double weight =1){
    try{
      fhmap1d.at(name)->Fill(value,weight);
    } catch(out_of_range e) {
      TH1F* newHist = new TH1F(name.c_str(),name.c_str(),bins,low,high);
      newHist->Fill(value,weight);
      fhlist->Add(newHist);
      fhmap1d[name] = newHist;
    }
  }
  void Fill(string name,
	    int binsX, double lowX, double highX, double valueX,
	    int binsY, double lowY, double highY, double valueY, 
	    double weight =1){
    try{
      fhmap2d.at(name)->Fill(valueX,valueY,weight);
    } catch(out_of_range e) {
      TH2F* newHist = new TH2F(name.c_str(),name.c_str(),
			       binsX,lowX,highX,
			       binsY,lowY,highY);
      newHist->Fill(valueX,valueY,weight);
      fhlist->Add(newHist);
      fhmap2d[name] = newHist;
    }
  }
  //RE New in v4.1_LT ->  New Fill function for 3d histos.
  void Fill(string name,
	    int binsX, double lowX, double highX, double valueX,
	    int binsY, double lowY, double highY, double valueY,
	    int binsZ, double lowZ, double highZ, double valueZ,
	    double weight =1){
    try{
      fhmap3d.at(name)->Fill(valueX,valueY,valueZ,weight);
    } catch(out_of_range e) {
      TH3F* newHist = new TH3F(name.c_str(),name.c_str(),
			       binsX,lowX,highX,
			       binsY,lowY,highY,
			       binsZ,lowZ,highZ);
      newHist->Fill(valueX,valueY,valueZ,weight);
      fhlist->Add(newHist);
      fhmap3d[name] = newHist;
    }
  }
  
  void FillHistogramsNoGate(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c);
  void FillHistogramsGateIn(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c,const char* inname);
  void FillHistogramsGateOut(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c,const char* outname);
  void FillHistogramsGateOnlyOut(GretinaCalc* gr, S800Calc* s800, Mode3Calc* m3c,const char* outname);

  //RE New in v4.1_LT -> Declaring functions for calculations in my analysis.
  double CasZangle(TVector3 posCompt, TVector3 posNext, const TVector3& decay);
  TVector3 CascadeZdecay(HitCalc* gammaKnown, double eTrueGammaKnown, double beta);
  TVector3 CascadeZdecay(TVector3 hitGammaKnown, double eLabGammaKnown, double eTrueGammaKnown, double beta);
  double CascadeCorrectedE(HitCalc* gammaOfInterest, const TVector3& decay, double beta);
  double CascadeCorrectedE(double eLabGammaOfInterest, double zHitGammaOfInterest, double xHitGammaOfInterest, double yHitGammaOfInterest, const TVector3& decay, double beta);
  double rho(TVector3 hit);
  double CalcSpan(HitCalc* gamma);
  
protected:
  TList* fhlist;
  map<string,TH1*> fhmap1d;
  map<string,TH2*> fhmap2d;
  map<string,TH3*> fhmap3d; 
  int fnentries;
  int fentry;
  char fcutfile[CUTFILE_NAMELENGTH];
  bool fhasfile;
  int ftac;
  int fCal;
  //RE New in v4.1_LT -> Adding fUpstream param.  If it is >0, then we do the cascade analysis.  
  int fUpstream;
  Settings* fSett;

  double Shifted_GammaKnown;
  double Shifted_GammaOfInterest;
  double Z_Tar_GammaKnown;
  double X_Tar_GammaKnown;
  double Y_Tar_GammaKnown;
  double Z_Focal_GammaKnown;
  double X_Focal_GammaKnown;
  double Y_Focal_GammaKnown;
  double A_Focal;
  double B_Focal;
  double c1;
  double c2;
  double c3;
  double Z_Focal_Decay;
  double X_Focal_Decay;
  double Y_Focal_Decay;
  //  double R_Tar_GammaKnown;
  double Z_Tar_GammaOfInterest;
  double X_Tar_GammaOfInterest;
  double Y_Tar_GammaOfInterest;
  double Z_Focal_GammaOfInterest;
  double X_Focal_GammaOfInterest;
  double Y_Focal_GammaOfInterest;
  double Z_Decay_GammaOfInterest;
  double X_Decay_GammaOfInterest;
  double Y_Decay_GammaOfInterest;
  //double R_Tar_GammaOfInterest;
  double Rho_Tar_GammaOfInterest;
  double Rho_Tar_GammaKnown;
  double Z_Decay_GammaKnown;
  double True_GammaKnown;
  double beta_r;
  double Z_Origin_Tar;
  double Z_Origin_FocalPoint;
  double RelGamma;
  double Theta_GammaKnown;
  double Z_Origin_Decay;
  double CascadeZ;
  double Theta_GammaOfInterest;
  double CorrectedE;
  double Z_Decay_GammaOfInterest_fake;
  double Theta_GammaOfInterest_fake;
  double CorrectedE_fake;
  
  //histo ranges
  int fstackpin_range[3]; //AR New in v4.1_TL 
  int fobj_range[3];
  int fxfp_range[3];
  int ftacobj_range[3];
  int ftacxfp_range[3];
  int fmobj_range[3];
  int fmxfp_range[3];
  int fIC_range[3];
  int fobjC_range[3];
  int fxfpC_range[3];
  int ftacobjC_range[3];
  int ftacxfpC_range[3];
  int fmobjC_range[3];
  int fmxfpC_range[3];
  double fPP_range[3];

};

#undef CUTFILE_NAMELENGTH

#endif

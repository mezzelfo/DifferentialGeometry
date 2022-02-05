(* ::Package:: *)

(* ::Package:: *)

BeginPackage["DifferentialGeometry`"]

VelocityNorm::usage = "Given a curve \[Alpha](t) returns the norm of the velocity vector \[Alpha]'(t)";
StationaryPoints::usage = "Given a cuve \[Alpha](t) returns the values of t for which \[Alpha](t) is a stationary point (\[Alpha]'(t)=0)";
LengthParameter::usage = "Given a curve \[Alpha](t) returns the length parameter s(t) defined by \!\(\*SubsuperscriptBox[\(\[Integral]\), \(a\), \(t\)]\)|\[Alpha]'(k)|\[DifferentialD]k";

FirstFundamentalForm::usage="Given a surface \[CapitalOmega](u,v) returns the First Fundamental Form's matrix";
AreaDensity::usage="Given a surface \[CapitalOmega](u,v) returns the area density scalar field for the surface";
OrthogonalParametrizationQ::usage="Given a surface \[CapitalOmega](u,v) returns True if the partial derivatives are orthogonal at any point";
Singularities::usage="Given a surface \[CapitalOmega](u,v) returns the points for which the tangent space cannot be defined or False if the surface is regular";
GaussMap::usage="Given a surface \[CapitalOmega](u,v) return the Gauss Map namely the vector field mapping each surface point to its normal versor";
SecondFundamentalForm::usage="Given a surface \[CapitalOmega](u,v) returns the Second Fundamental Form's matrix";
ShapeOperator::usage="Given a surface \[CapitalOmega](u,v) returns the Shape Operator's matrix";
PrincipalCurvatures::usage="Given a surface \[CapitalOmega](u,v) returns a vector containing the eigenvalues of the Shape Operator";
GaussianCurvature::usage="Given a surface \[CapitalOmega](u,v) returns the Gaussian Curvature";
MeanCurvature::usage="Given a surface \[CapitalOmega](u,v) returns the Mean Curvature";
PrincipalParametrizationQ::usage="Given a surface \[CapitalOmega](u,v) returns True if its parametrization is principal namely the the coordinated lines are also curvature lines";
EllipticPoints::usage="Given a surface \[CapitalOmega](u,v) returns the values of u and v such that \[CapitalOmega](u,v) is an elliptic point namely its gaussian curvature is positive";
HyperbolicPoints::usage="Given a surface \[CapitalOmega](u,v) returns the values of u and v such that \[CapitalOmega](u,v) is an hyperbolic point namely its gaussian curvature is negative";
PlanarPoints::usage="Given a surface \[CapitalOmega](u,v) returns the values of u and v such that \[CapitalOmega](u,v) is a planar point namely its gaussian curvature is 0";
UmbilicalPoints::usage="Given a surface \[CapitalOmega](u,v) returns the values of u and v such that \[CapitalOmega](u,v) is an umbilical point namely the principal curvatures are equal";

Begin["`Private`"]

(*Curve*)
VelocityNorm[\[Alpha]_,t_,assumptions_:True]:=FullSimplify[Norm@Evaluate@(D[\[Alpha],t]),assumptions]
StationaryPoints[\[Alpha]_,t_,assumptions_:True]:=Reduce[VelocityNorm[\[Alpha],t,assumptions]==0&&assumptions,t]
LengthParameter[\[Alpha]_,t_,domain_,assumptions_:True]:=Integrate[VelocityNorm[\[Alpha],t,assumptions],domain,assumptions]
(*Reparametrize[\[Alpha]_,t_,domain_,assumptions_]:=Evaluate[\[Beta][t]/.NDSolve[{(\[Beta]^\[Prime])[t]\[Equal]1/VelocityNorm[][\[Beta][t]],\[Beta][0]\[Equal] 0},{\[Beta]},{t,0,L}]][[1]];*)

(*Superfici*)
FirstFundamentalForm[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Transpose[D[\[CapitalOmega],{{u,v}}]].D[\[CapitalOmega],{{u,v}}],assumptions];
AreaDensity[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Sqrt[Det[FirstFundamentalForm[\[CapitalOmega],{u,v}]]],assumptions];
OrthogonalParametrizationQ[\[CapitalOmega]_,{u_,v_}]:=DiagonalMatrixQ[FirstFundamentalForm[\[CapitalOmega],{u,v}]];
Singularities[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=Reduce[Norm[Cross@@Transpose@D[\[CapitalOmega],{{u,v}}]]==0&&assumptions,{u,v},Reals];
GaussMap[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Normalize[Cross@@Transpose@D[\[CapitalOmega],{{u,v}}]],assumptions];
SecondFundamentalForm[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Transpose[D[\[CapitalOmega],{{u,v},2}],{3,1,2}].GaussMap[\[CapitalOmega],{u,v},assumptions],assumptions];
ShapeOperator[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Inverse[FirstFundamentalForm[\[CapitalOmega],{u,v},assumptions]].SecondFundamentalForm[\[CapitalOmega],{u,v},assumptions],assumptions];
PrincipalCurvatures[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Eigenvalues[ShapeOperator[\[CapitalOmega],{u,v},assumptions]],assumptions];
GaussianCurvature[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[Det[ShapeOperator[\[CapitalOmega],{u,v},assumptions]],assumptions];
MeanCurvature[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=FullSimplify[1/2 Tr[ShapeOperator[\[CapitalOmega],{u,v},assumptions]],assumptions];
PrincipalParametrizationQ[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=DiagonalMatrixQ[ShapeOperator[\[CapitalOmega],{u,v},assumptions]];
EllipticPoints[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=Reduce[GaussianCurvature[\[CapitalOmega],{u,v},assumptions]>0&&assumptions,{u,v},Reals];
HyperbolicPoints[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=Reduce[GaussianCurvature[\[CapitalOmega],{u,v},assumptions]<0&&assumptions,{u,v},Reals];
PlanarPoints[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=Reduce[GaussianCurvature[\[CapitalOmega],{u,v},assumptions]==0&&assumptions,{u,v},Reals];
UmbilicalPoints[\[CapitalOmega]_,{u_,v_},assumptions_:True]:=Module[{k=PrincipalCurvatures[\[CapitalOmega],{u,v},assumptions]},Reduce[k[[1]]==k[[2]]&&assumptions,{u,v},Reals]];

End[]
EndPackage[]




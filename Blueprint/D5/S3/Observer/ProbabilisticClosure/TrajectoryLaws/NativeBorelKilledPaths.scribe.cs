using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelKilledPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula f=F.Id("F"), g=F.Id("G"), q=F.Id("Q"), r=F.Id("R"), n=F.Id("n"),
            test=F.Id("phi"), sub=F.Id("hsub");
        Formula m=Call("doob",f,g), hq=Call("threeStepAverage",f,q);
        Formula survival=Call("sequence",n,Call("iterate",m,Call("one"),n,q));
        Formula killing=Call("toReal",Seq(D(1),Minus,Call("mass",m,q,Call("univ"))));
        Formula statement=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Exists,Sp,sub,Colon,Sp,Call("Subprobability",m),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),
            Land,Sp,Call("IsMarkovKernel",Call("cemetery",m)),Land,Sp,
            Call("IsProbabilityMeasure",Call("killedTrajectory",f,m,sub)),Land,Sp,
            Open,Forall,Sp,q,Colon,Sp,F.Id("PDescriptor"),Comma,Sp,
                Call("AbsolutelyContinuous",Call("row",m,q),Call("CRow",f,q)),Close,Land,Sp,
            Open,Forall,Sp,q,InMacro,Sp,g,Comma,Sp,Call("CoreAt",f,q),Land,Sp,
                Call("AE",Call("CRow",f,q),r,Seq(r,InMacro,Sp,g)),Close,Land,Sp,
            Open,Forall,Sp,test,Colon,Sp,Call("Function",F.Id("PDescriptor"),F.Id("ENNReal")),Comma,Sp,
                Call("Measurable",test),Rightarrow,Forall,Sp,n,Colon,Sp,F.Id("Nat"),Comma,Sp,
                Forall,Sp,q,InMacro,Sp,g,Comma,Sp,
                Call("normalizedIterate",f,Call("productFunction",Call("threeStepAverage",f),test),n,q),
                Eq,Multiply(hq,Call("iterate",m,test,n,q)),Close,Land,Sp,
            Call("AE",Call("nuP",f),q,Seq(Call("Antitone",survival),Land,Sp,
                Call("Tendsto",survival,F.Id("atTop"),Call("nhds",Fraction(Call("q",f,q),hq))))),
            Land,Sp,Open,Forall,Sp,q,InMacro,Sp,g,Comma,Sp,D(0),Lt,
                Call("mass",m,q,Call("univ")),Close,Land,Sp,
            Call("AE",Call("nuP",f),q,Seq(killing,Eq,Fraction(Call("delta",f,q),Call("h",f,q)),
                Land,Sp,Multiply(Fraction(D(2),D(3)),Call("excess",q)),Le,killing)),Land,Sp,
            Call("AE",Call("nuP",f),q,Seq(
                Call("smul",Pow(Call("endpointRate"),Seq(Minus,D(1))),Call("LRow",f,q)),Le,
                Call("smul",Call("ofReal",Seq(D(1),Plus,Fraction(Multiply(D(2,5),Call("excess",q)),D(9)))),
                    Call("CRow",f,q)))));
        Formula native=Call("nativeEndpoint",F.Id("p"),Call("true"));
        Formula rowImmortal=Call("mass",Call("startedTrajectory",m,sub,q),Call("immortal"));
        Formula infiniteStatement=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Exists,Sp,sub,Colon,Sp,Call("Subprobability",m),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),
            Land,Sp,Open,Forall,Sp,q,InMacro,Sp,g,Comma,Sp,Forall,Sp,n,Colon,Sp,F.Id("Nat"),
                Comma,Sp,D(0),Lt,Call("iterate",m,Call("one"),n,q),Close,
            Land,Sp,Call("AE",Call("nuP",f),q,Seq(rowImmortal,Eq,Fraction(Call("q",f,q),hq),
                Land,Sp,rowImmortal,Eq,Call("If",Seq(q,Eq,native),D(1),D(0)))),Land,Sp,
            Call("mass",Call("killedTrajectory",f,m,sub),Call("immortal")),Eq,
                Call("mass",Call("nuP",f),Call("singleton",native)));
        Formula path=F.Id("omega"), radius=F.Id("R");
        Formula xi=Call("restrict",Call("killedTrajectory",f,m,sub),Call("immortal"));
        Formula original=Call("map",Call("originalTrajectory",f),Call("includePath"));
        Formula nativeMass=Call("mass",Call("nuP",f),Call("singleton",native));
        Formula nativePath=Call("constantPath",Call("inl",native));
        Formula identityStatement=Seq(Forall,Sp,f,Colon,Sp,F.Id("CommonFlow"),Comma,Sp,
            Exists,Sp,g,Subset,Sp,F.Id("PDescriptor"),Comma,Sp,
            Exists,Sp,sub,Colon,Sp,Call("Subprobability",m),Comma,Sp,
            Call("MeasurableSet",g),Land,Sp,Call("AE",Call("nuP",f),q,Seq(q,InMacro,Sp,g)),
            Land,Sp,Open,Forall,Sp,q,InMacro,Sp,g,Comma,Sp,Forall,Sp,n,Colon,Sp,F.Id("Nat"),
                Comma,Sp,D(0),Lt,Call("iterate",m,Call("one"),n,q),Close,
            Land,Sp,xi,Eq,Call("smul",nativeMass,Call("dirac",nativePath)),Land,Sp,
            xi,Eq,Call("map",Call("restrict",Call("originalTrajectory",f),
                Call("event",path,Seq(Call("at",path,D(0)),Eq,native))),Call("includePath")),
            Land,Sp,xi,Le,original,Land,Sp,Call("AbsolutelyContinuous",xi,original),Land,Sp,
            Call("AE",xi,path,Seq(Call("pathDefect",path),Eq,D(0))),Land,Sp,
            Open,Forall,Sp,radius,Colon,Sp,F.Id("Real"),Comma,Sp,D(0),Le,Sp,radius,Rightarrow,
                Call("restrict",xi,Call("event",path,Seq(Call("pathDefect",path),Le,
                    Call("ofReal",radius)))),Le,
                Call("smul",Multiply(Fraction(D(2,5),D(6)),Call("ofReal",Call("exp",
                    Fraction(Multiply(D(2,5),radius),D(9))))),original),Close,Land,Sp,
            Open,Forall,Sp,n,Colon,Sp,F.Id("Nat"),Comma,Sp,
                Call("withDensity",Call("killedTrajectory",f,m,sub),Call("densityAt",f,n)),Eq,xi,
                Land,Sp,Call("withDensity",Call("prefix",Call("killedTrajectory",f,m,sub),n),
                    Call("terminalDensity",f,n)),Eq,Call("prefix",xi,n),Close);
        return DocumentDefinition.Create(ScribeNode.Create("Killed Doob paths on the original flow",
            H("A Markov cemetery extension"),Blocks(
                Paragraph(Text("F is the original boxed Borel CommonFlow and G is an earned measurable conull absorbing carrier. Write h=threeStepAverage and T=L/(6/25). On G, doob(F,G) has density h(R)/(h(Q)*(6/25)) with respect to the actual L row; it is the zero row outside G. Subprobability(M) means every M row has mass at most one. Cemetery is the disjoint union of the original descriptor space and one absorbing state. The extension sends each live row through the inclusion and sends its missing mass to that state. killedTrajectory is its full Ionescu-Tulcea law with initial law nuP mapped through the inclusion. It is formed from the Markov extension, while M remains substochastic.")),
                Describe.Lean(DescribeId.Create("common-flow-doob-survival"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_doob_survival"),
                    H("Finite conjugacy and limiting survival"),StatementSource.FromAuthor(Disp(statement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("For every nonnegative measurable test phi, multiplying the M iterate by h gives the normalized L iterate of h*phi on G. This is proved at every finite depth using absorption and cancellation of the positive finite h factors. With phi=1, M^n1 decreases to q/h. The cemetery extension is a probability kernel and therefore supplies a full trajectory probability measure. Its construction and the finite conjugacy are distinct from an identity for the immortal restriction of that measure.")),
                    Paragraph(Text("Every live row has positive mass, using L>=(1/5)C and the core lower bound h>=3/25. Almost everywhere the killing probability is delta/h and is at least (2/3)*excess, since delta>=excess/3 and h<=1/2. The same original completion coordinate supplies T<=(1+25*excess/9)C. These two bounds use the same acquired flow and the same excess."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-immortal-survival"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_immortal_survival"),
                    H("Probability of surviving forever"),StatementSource.FromAuthor(Disp(infiniteStatement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("immortal is the measurable event that no coordinate equals the cemetery state. startedTrajectory is the lawful cemetery process from the specified original descriptor. Its finite-time live probability is M^n1, and every finite iterate is strictly positive on G. This follows by induction from positive row mass and absorption of the same carrier. The absorbing cemetery makes the finite live events decrease almost everywhere, so continuity from above identifies the immortal probability with their infimum. The earned limit q/h therefore supplies the actual infinite-event probability almost everywhere under the original margin, including zero native mass. Integrating that probability gives precisely the upper native singleton mass. Positive finite survival is compatible with zero immortal mass."))),DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("common-flow-immortal-identity"),
                    DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelKilledPaths.common_flow_immortal_identity"),
                    H("The complete immortal path measure"),StatementSource.FromAuthor(Disp(identityStatement)),
                    AssessedProvenance.FromRepo(),Blocks(Paragraph(Text("originalTrajectory is the full homogeneous law of the actual C kernel with initial law nuP. includePath includes every original coordinate into the cemetery sum. The immortal restriction equals that original law restricted to the upper native initial descriptor and then included into the cemetery path space. More precisely it is the upper native atom mass times the Dirac law of the constant upper native path. On a positive native atom the original residual and successor results force C and M to be its actual Dirac row. The finite prefix masses and continuity from above identify the complete constant path. Its mass equals the total immortal mass, which proves equality on the full path sigma-algebra.")),
                    Paragraph(Text("pathDefect is the sum over all times of the nonnegative real excess converted to ENNReal, with zero at the cemetery. The original excess is nonnegative on the original conull core. This series is zero almost everywhere under the immortal restriction. The whole immortal measure is dominated by the included original C law and is absolutely continuous with respect to it. In particular its restriction to pathDefect<=R, for every R>=0, satisfies the original local comparison constant (25/6)*exp(25R/9), obtained from h<=1/2, h>=3/25 and c=9/25.")),
                    Paragraph(Text("Define terminalSurvival(F,inl(Q))=q(F,Q)/threeStepAverage(F,Q) and terminalSurvival(F,inr(unit))=0. densityAt(F,n) evaluates this function at time n on a full path; terminalDensity(F,n) evaluates it at the last coordinate of the prefix through n. prefix(mu,n) is the pushforward of mu under restriction to times zero through n. For every finite n, weighting the complete killed trajectory by densityAt(F,n) equals its immortal restriction. Consequently the immortal prefix is the killed prefix weighted by the terminal factor at X_n. The factor is preserved by the actual Doob action: harmonicity of q, cancellation of positive h, row absolute continuity and stationarity imply that its total expected mass is always the original native atom mass. The constant native path carries that whole mass, which proves the weighted identity on the full path sigma-algebra and then on each finite prefix."))),DescribeRole.Theorem))));
    }
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Grp(a), Caret, Grp(b));
}

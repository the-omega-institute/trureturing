using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class NativeBorelRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelRepresentation.";
    public DocumentDefinition Create()
    {
        Formula s=F.Id("s"), r=F.Id("r"), t=F.Id("t"), d=F.Id("D"), n=F.Id("n"), j=F.Id("j"), i=F.Id("i"), b=F.Id("b"), q=F.Id("Q"), w=F.Id("W"), theta=F.Id("theta"), flow=F.Id("F"), nu=F.Id("nu"), kernel=F.Id("K");
        return DocumentDefinition.Create(ScribeNode.Create("Complete legal-law representation", H("Coordinates and full residuals"), Blocks(
            Paragraph(Text("ProbabilityMeasure(ValidTail(s)) is the existing probability-law carrier, and Regular is exactly the source emission interval and all source tail bounds. Infinity remains in ValidTail and in every coordinate comparison. Simplex(s) consists of all ENNReal coordinate functions with countable sum one. No finite-support condition is imposed.")),
            Node("coordinateEquiv",All(Call("MeasurableEquiv",Call("coordinateEquiv",s),Call("ProbabilityMeasure",Call("ValidTail",s)),Call("Simplex",s)),("s","ActivePhase")),"The forward map takes every singleton mass. The inverse is the countable sum of mass(t) times Dirac(t). Singleton reconstruction proves both inverse identities, and measurable evaluation and countable sums prove measurability in both directions. This identifies Giry with complete-coordinate measurability. The complete-coordinate topology theorem uses this equivalence and the finite TV estimate to identify the original TV topology and Borel sets for all laws.",DescribeRole.Definition),
            Node("regular_measurable",All(Call("MeasurableSet",Call("RegularSet",s)),("s","ActivePhase")),"RegularSet(s) is the set of probability laws D satisfying Regular(s,D), with the unchanged interval [1/3,2/5], tail rate 4/15, and suspended tail factor 2/5. Each inequality is measurable and the intersection is countable. The explicit simplex equivalence transports standard-Borel structure to probability laws; this measurable regularity set then gives the original RegularDescriptor subtype standard-Borel structure."),
            Node("regular_infinity_zero",All(Eqn(Mass(Call("law",d),Call("infinity",s)),Num(0)),("s","ActivePhase"),("D","RegularDescriptor")),"D ranges over RegularDescriptor(s). Every tailSet(s,j) contains infinity. Its mass bounds that singleton and tends to zero, including the suspended factor. Infinity is retained as a coordinate; its zero mass is derived from regularity."),
            Node("residualB_measurable",Call("Measurable",Call("residualB")),"residualB maps PDescriptor into the entire measure space on ValidTail(beta). The range of prependB is the complement of the first alpha atom. Its comap mass is exactly 1-u, so the normalized residual is a probability measure. The reciprocal is finite because 3/5 <= 1-u <= 2/3. No opposite regularity premise is used."),
            Node("residualA_measurable",Call("Measurable",Call("residualA")),"residualA maps BDescriptor into the entire measure space on ValidTail(p). The range of prependA is the complement of betaStop. Its comap mass is v and 1/3 <= v <= 2/5, so normalization gives a probability measure. Comap evaluation and the same original input emission give measurability."),
            Node("tv_finite_coordinate_bound", All(Le(Call("TV",F.Id("P"),F.Id("Q")),Call("ofReal",Call("finiteCoordinateGapPlusTail",F.Id("P"),F.Id("Q"),F.Id("F")))),("s","ActivePhase"),("P","ProbabilityMeasureValidTail"),("Q","ProbabilityMeasureValidTail"),("F","FinsetValidTail")), "P and Q range over all probability laws on ValidTail(s), and F is any finite set of complete atoms. finiteCoordinateGapPlusTail means sum over t in F of abs[P.real{t}-Q.real{t}] plus P.real(complement F). TV is exactly the repository event-supremum of the maximum of the two ENNReal directed differences. Split an event over F and its complement; the reverse difference follows by applying the same bound to the complementary event and using both total masses equal to one. This establishes the finite-coordinate TV neighborhood estimate without assuming a weak-topology identification. Finite approximation and both neighborhood directions establish the corresponding topology and Borel equality in NativeBorelTVTopology."))));
    }
    private static DocumentBlock.Describe Node(string declaration, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create(declaration.Replace('_','-').ToLowerInvariant()), DeclarationHandle.Create(Prefix+declaration),
        H(declaration.Replace('_',' ')), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Eq, b);
    private static Formula All(Formula body, params (string Name,string Type)[] xs) {
        for(int k=xs.Length-1;k>=0;k--) body=Seq(Forall,Sp,F.Id(xs[k].Name),Colon,Sp,F.Id(xs[k].Type),Comma,Sp,body);
        return body;
    }
    private static Formula Mass(Formula law, Formula atom) => Call("mass",law,atom);
}

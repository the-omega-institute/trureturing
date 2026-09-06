using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Existence;

internal sealed class QubitEmpiricalImageReflexiveGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact qubit density-state readout is predicate-complete on its image but reflexively incomplete.",
        H("Qubit Empirical-Image Reflexive Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qubit-empirical-image-reflexive-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Existence/QubitEmpiricalImageReflexiveGap."
                        + "qubit_empirical_image_reflexive_gap"),
                H("Qubit empirical completeness does not imply reflexive completeness"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a three-context rank-one qubit observer whose readout R is "
                            + "injective on the full density-state subtype.")),
                    Paragraph(Text(
                        "For that same R, pullback from Boolean predicates on its realized range "
                            + "is bijective, while every density-state-indexed catalog into that "
                            + "predicate space is non-surjective.")),
                    Paragraph(Text(
                        "This specializes the abstract strict-gap theorem to the existing public "
                            + "qubit witness. It does not include concrete context-subfamily "
                            + "minimality because the source Pauli context is private."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula context = F.Id("C");
        Formula state = F.Id("rho");
        Formula readout = F.Id("R_C");
        Formula catalog = F.Id("catalog");
        Formula fin2 = Call("Fin", F.D(2));
        Formula fin3 = Call("Fin", F.D(3));
        Formula density = Call("DensityState", fin2);
        Formula contextType = Arrow(fin3, Call("RankOneContext", F.D(2)));
        Formula range = Call("range", readout);
        Formula predicate = Arrow(range, F.Id("Bool"));
        Formula catalogType = Arrow(density, predicate);
        Formula readoutBody = Call("contextReadout", context,
            Call("CStarMatrix.ofMatrix.symm", Call("value", state)));

        return F.Disp(F.Seq(
            F.Exists, F.Sp, context, F.Colon, F.Sp, contextType, F.Comma,
            F.RowBreak, F.Grp(),
            Call("let", readout, F.Colon, Arrow(density,
                Arrow(fin3, Arrow(fin2, Seq(F.Mathbb, F.Grp(F.Id("C")))))),
                Call("fun", state, readoutBody)), F.Comma,
            F.RowBreak, F.Grp(), Call("Injective", readout), F.Sp, F.Land,
            F.RowBreak, F.Grp(), Call("Bijective", Call("observablePullback", readout)),
            F.Sp, F.Land, F.RowBreak, F.Grp(),
            F.Forall, F.Sp, catalog, F.Colon, F.Sp, catalogType, F.Comma, F.Sp,
            F.Neg, F.Sp, Call("Surjective", catalog), F.Dot));
    }
}

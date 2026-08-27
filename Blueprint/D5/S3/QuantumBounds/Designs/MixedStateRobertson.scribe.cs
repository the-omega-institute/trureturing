using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class MixedStateRobertsonDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/QuantumBounds/Designs/MixedStateRobertson."
            + "mixed_state_robertson_uncertainty";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mixed-state standard deviations bound the expected commutator magnitude.",
        H("Mixed-State Robertson Uncertainty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-state-robertson-uncertainty"),
                DeclarationHandle.Create(Declaration),
                H("Mixed-state Robertson uncertainty"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let d be a finite index type with decidable equality, rho a canonical "
                            + "density state, and A and B Hermitian complex square matrices. "
                            + "The density-state carrier supplies positivity and trace-one "
                            + "normalization.")),
                    Paragraph(Text(
                        "The underlying density matrix and its positive continuous-functional-"
                            + "calculus square root construct the centered GNS vectors u and v. "
                            + "Their Frobenius norms are the two standard deviations.")),
                    Paragraph(Text(
                        "Cauchy-Schwarz bounds the weighted cross pairing, whose imaginary part "
                            + "is one half of the expected commutator. This gives the displayed "
                            + "Robertson inequality for mixed as well as pure density states."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula rhoMatrix = F.Id("rhoMatrix");
        Formula stateRoot = F.Id("stateRoot");
        Formula matrixCarrier = Call("Matrix", d, d, Seq(Mathbb, Grp(F.Id("C"))));
        Formula Centered(Formula observable) => Seq(
            Open, observable, Minus,
            Operatorname, Grp(F.Id("Tr")), Open, rhoMatrix, Cdot, Sp, observable, Close,
            Cdot, Sp, F.Id("I"), Close);
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula Norm(Formula value) => Seq(
            Vert, Sp, value, Vert, Underscore, Grp(F.Id("HS")));
        Formula Abs(Formula value) => Seq(Vert, Sp, value, Vert);
        Formula commutator = Seq(Open, F.Id("A"), F.Id("B"), Minus,
            F.Id("B"), F.Id("A"), Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, d, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
                OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, d, Close,
                CloseBracket, Comma, Sp,
                OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, d, Close,
                CloseBracket, Comma),
            Seq(
                Forall, Sp, Rho, Colon, Sp, Call("DensityState", d), Comma, Sp,
                F.Id("A"), Comma, Sp, F.Id("B"), Colon, Sp, matrixCarrier, Comma),
            Seq(
                Operatorname, Grp(F.Id("Hermitian")), Open, F.Id("A"), Close,
                Sp, Land, Sp,
                Operatorname, Grp(F.Id("Hermitian")), Open, F.Id("B"), Close,
                Sp, Rightarrow, Sp),
            Seq(
                Open, rhoMatrix, Colon, Eq, Call("toMatrix", Rho), Close,
                Sp, Land, Sp,
                Open, stateRoot, Colon, Eq, Sqrt, Grp(rhoMatrix), Close,
                Sp, Land, Sp),
            Seq(
                Open, u, Colon, Eq, Centered(F.Id("A")), Cdot, Sp, stateRoot, Close,
                Sp, Land, Sp,
                Open, v, Colon, Eq, Centered(F.Id("B")), Cdot, Sp, stateRoot, Close,
                Sp, Rightarrow, Sp),
            Seq(
                Norm(u), Norm(v), Sp, Geq, Sp,
                Frac, Grp(D(1)), Grp(D(2)),
                Abs(Seq(Operatorname, Grp(F.Id("Tr")), Open,
                    rhoMatrix, Cdot, Sp, commutator, Close)), Dot),
        ]));
    }
}

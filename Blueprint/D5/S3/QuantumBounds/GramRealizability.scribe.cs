using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class GramRealizabilityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/QuantumBounds/GramRealizability.gram_realizability";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Hilbert-space operators are exactly adjoint-square Gram operators.",
        H("Gram Realizability"),
        Blocks(Describe.Lean(
            DescribeId.Create("gram-realizability"),
            DeclarationHandle.Create(Declaration),
            H("Positivity is equivalent to a Gram factorization"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let V be a complete complex inner-product space and Q a continuous "
                        + "linear endomorphism of V. Positivity is understood in the standard "
                        + "Loewner order on bounded operators.")),
                Paragraph(Text(
                    "The source uses Q both as an operator and as a two-variable form. The "
                        + "formal statement resolves this ambiguity by defining the form as "
                        + "the inner product of Qx with y.")),
                Paragraph(Text(
                    "If Q is positive, its continuous-functional-calculus square root is a "
                        + "canonical witness O on V. It is self-adjoint and its square is Q. "
                        + "Conversely, every adjoint-square operator is positive.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the positive square-root identities and the "
                        + "positivity theorem for adjoint compositions; the proof uses these "
                        + "results directly."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula space = F.Id("V");
        Formula q = F.Id("Q");
        Formula o = F.Id("O");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula operators = Seq(Operatorname, Grp(F.Id("B")), Open, space, Close);
        Formula Apply(Formula function, Formula argument) =>
            Seq(function, Open, argument, Close);
        Formula Inner(Formula left, Formula right) =>
            Seq(Langle, Sp, left, Comma, Sp, right, Sp, Rangle,
                Underscore, Grp(complex));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, space, Colon, Sp,
                Operatorname, Grp(F.Id("Hilbert")), Open, complex, Close,
                Comma, Sp, q, Colon, Sp, operators, Comma),
            Seq(
                q, Sp, Geq, Sp, D(0), Sp, Leftrightarrow, Sp,
                Exists, Sp, o, Colon, Sp, operators, Comma),
            Seq(
                q, Sp, Eq, Sp, o, Caret, Grp(Star), Sp, o,
                Sp, Land, Sp),
            Seq(
                Forall, Sp, x, Comma, Sp, y, InMacro, Sp, space, Comma, Sp,
                Inner(Apply(q, x), y), Sp, Eq, Sp,
                Inner(Apply(o, x), Apply(o, y)), Dot),
        ]));
    }
}

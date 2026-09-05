using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Hardy;

internal sealed class PhaseFibreClarkBasisDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Hardy/PhaseFibreClarkBasis."
            + "phase_fibre_is_orthonormal_basis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full-cardinality orthonormal phase fibre is an orthonormal basis of its "
            + "finite-dimensional model space.",
        H("Phase-Fibre Clark Basis"),
        Blocks(Describe.Lean(
            DescribeId.Create("phase-fibre-is-orthonormal-basis"),
            DeclarationHandle.Create(Declaration),
            H("The normalized phase fibre is a complete orthonormal basis"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let e be the family of normalized boundary kernels indexed by the m "
                        + "points of one regular phase fibre. If the kernel identity makes "
                        + "this family orthonormal and the model space has dimension m, then "
                        + "e is the underlying family of an orthonormal basis.")),
                Paragraph(Text(
                    "The finite-dimensional assumption is explicit. A bare Lean finrank "
                        + "equality would not carry the source's dimension meaning in the "
                        + "zero-dimensional case unless finite dimensionality were already "
                        + "known.")),
                Paragraph(Text(
                    "Pinned Mathlib supplies the whole linear-algebraic step. Orthonormal."
                        + "linearIndependent gives independence, LinearIndependent."
                        + "span_eq_top_of_card_eq_finrank' upgrades the m vectors to a "
                        + "spanning family, and OrthonormalBasis.mk packages the resulting "
                        + "basis. The Blaschke boundary-cover construction, kernel "
                        + "orthogonality, and normalization identities remain separate "
                        + "analytic inputs."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula scalar = F.Id("K");
        Formula space = F.Id("H");
        Formula m = F.Id("m");
        Formula family = F.Id("e");
        Formula basis = F.Id("b");
        Formula index = F.Id("j");
        Formula finM = Call("Fin", m);

        return Disp(new Formula.Aligned([
            Seq(
                Call("Orthonormal", scalar, family), Sp, Land, Sp,
                Call("finrank", scalar, space), Sp, Eq, Sp, m, Sp,
                Rightarrow),
            Seq(
                Exists, Sp,
                Typed(basis, Call("OrthonormalBasis", finM, scalar, space)),
                Comma),
            Seq(
                Forall, Sp, index, Sp, InMacro, Sp, finM, Comma, Sp,
                Call("apply", basis, index), Sp, Eq, Sp,
                Call("apply", family, index), Dot),
        ]));
    }

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var item = 0; item < arguments.Length; item++)
        {
            if (item > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[item]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }
}

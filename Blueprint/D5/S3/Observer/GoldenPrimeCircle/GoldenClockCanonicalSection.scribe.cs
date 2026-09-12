using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockCanonicalSectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockCanonicalSection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The alpha-cut lift equals dev's actual canonical betaGolden object. "
                + "Its scale maps compose, while anchored extra-return maps can "
                + "retain a nonzero order defect.",
            H("Canonical Zeckendorf Section Bridge"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-canonical-object-equality"),
                    DeclarationHandle.Create(Prefix + "canonical_lift_eq_betaGolden"),
                    H("The new lift and the existing canonical object are equal"),
                    StatementSource.FromAuthor(EqualityFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural n, lift(alpha,n)="
                                + "floor((n+1)*alpha)+n*phi equals betaGolden(n) "
                                + "in the existing GoldenInt ring. The proof imports "
                                + "BetaBeattyClosedForms, the actual displacement-decode "
                                + "theorem, and the injective real embedding.")),
                        Paragraph(Text(
                            "betaGolden_scale_covariance binds multiplication by "
                                + "phi^(L+2) to the original canonical objects. Its natural "
                                + "output index is the nonnegative integer layer(alpha,L,n), "
                                + "with the coercion back to Nat proved explicitly."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-canonical-composition"),
                    DeclarationHandle.Create(Prefix + "canonical_layer_compose"),
                    H("Canonical scale maps compose without a relifting correction"),
                    StatementSource.FromAuthor(CompositionFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The statement quantifies over every natural K,L and every "
                                + "integer n, including zero. A direct residual bound proves "
                                + "canonical_carry_zero. centered_layer_compose separately "
                                + "proves the analogous centered-cut identity.")),
                        Paragraph(Text(
                            "entry_as_anchored_canonical_shift states the exact relation "
                                + "entry(L,m)=F(L+3)+layer(alpha,L,m-1). The old return "
                                + "index and the canonical scale are distinct operations.")),
                        Paragraph(Text(
                            "no_common_injective_intertwiner proves that an old pair "
                                + "with nonzero computed commutator cannot be converted to "
                                + "this canonical commuting pair by one injective relabeling "
                                + "intertwining both maps. Changing the section therefore "
                                + "must not be described as preserving the old dynamics."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula EqualityFormula() => Disp(Seq(
        Call("lift", F.Id("alpha"), F.Id("n")), Sp, Eq, Sp,
        Call("betaGolden", F.Id("n"))));

    private static Formula CompositionFormula() => Disp(Seq(
        Call("layer", F.Id("alpha"), F.Id("K"),
            Call("layer", F.Id("alpha"), F.Id("L"), F.Id("n"))),
        Sp, Eq, Sp,
        Call("layer", F.Id("alpha"), Seq(F.Id("K"), Plus, F.Id("L"), Plus, F.Id("2")),
            F.Id("n"))));
}

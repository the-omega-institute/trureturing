using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockSectionAlgebraDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockSectionAlgebra.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "The selected lift lives in the existing golden-integer ring. "
                + "Its projection defect is cut-dependent; internally contractive "
                + "multiplication admits a centered invariant section, but no "
                + "additive section is invariant under a nonrational multiplier.",
            H("Golden Integer Sections and Projection Defects"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-section-product-defect"),
                    DeclarationHandle.Create(Prefix + "projected_compose"),
                    H("Exact composition defect for arbitrary golden multipliers"),
                    StatementSource.FromAuthor(ProductFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every golden integer u,v, real offset rho and integer n, "
                                + "lift(rho,n)=floor(n*alpha+rho)+n*phi. projected(u,rho,n) "
                                + "is the phi-coordinate of u*lift(rho,n). The integer "
                                + "carry(v,rho,n) is proved equal to "
                                + "floor(internal(v)*residual(rho,n)+rho).")),
                        Paragraph(Text(
                            "internal is the existing real embedding composed with "
                                + "Galois conjugation. Both faces are real embeddings. "
                                + "No complex imaginary coordinate is assigned to an "
                                + "ordinary integer."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-centered-invariant-section"),
                    DeclarationHandle.Create(Prefix + "centered_lift_projected"),
                    H("A common centered section preserves all contractive multipliers"),
                    StatementSource.FromAuthor(CenteredFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Here c=1/2 and the hypothesis is abs(internal(u))<=1. "
                                + "The statement holds for all integers n, including zero. "
                                + "Irrationality excludes half-integer ties. The proof uses "
                                + "the strict centered residual bound and the actual floor "
                                + "definition, rather than an assumed invariance field.")),
                        Paragraph(Text(
                            "centered_commute and run_eq_projected_product prove "
                                + "simultaneous commutation and exact arbitrary finite-word "
                                + "composition. Changing rho changes the selected maps; "
                                + "this is not a conjugacy assertion about the old floor maps.")),
                        Paragraph(Text(
                            "no_additive_invariant_section proves that any additive "
                                + "section s of the phi-coordinate fails invariance under "
                                + "every u with u.b nonzero. Invariance would force the "
                                + "integer a=(s(1)).a to satisfy a*a+a=1. Thus the centered "
                                + "multiplicative construction cannot silently preserve "
                                + "ordinary integer addition as well."))),
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

    private static Formula ProductFormula() => Disp(Seq(
        Call("projected", F.Id("u"), F.Id("rho"),
            Call("projected", F.Id("v"), F.Id("rho"), F.Id("n"))),
        Sp, Eq, Sp,
        Call("projected", Seq(F.Id("u"), Cdot, F.Id("v")), F.Id("rho"), F.Id("n")),
        Sp, Plus, Sp, Call("b", F.Id("u")), Cdot,
        Call("carry", F.Id("v"), F.Id("rho"), F.Id("n"))));

    private static Formula CenteredFormula() => Disp(Seq(
        Call("lift", F.Id("c"), Call("projected", F.Id("u"), F.Id("c"), F.Id("n"))),
        Sp, Eq, Sp, F.Id("u"), Cdot, Call("lift", F.Id("c"), F.Id("n"))));
}

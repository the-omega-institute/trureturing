using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Quotients;

internal sealed class RelativeIdentityRefinementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finer readout quotient maps uniquely and surjectively onto every "
        + "factored coarse quotient.",
        H("Relative Identity Refinement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-identity-is-antitone-under-readout-refinement"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Quotients/RelativeIdentityRefinement."
                    + "relative_identity_refinement"),
                H("Refinement induces the canonical quotient surjection"),
                StatementSource.FromAuthor(RelativeIdentityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a coarse readout factor through a fine readout. Equality under the "
                        + "fine readout then implies equality under the coarse readout, so the "
                        + "fine kernel relation is contained in the coarse kernel relation.")),
                    Paragraph(Text(
                        "Mathlib's Setoid.map_of_le constructs the induced quotient map from "
                        + "that relation inclusion. Every coarse class has the same underlying "
                        + "representative in the fine quotient, which proves surjectivity. "
                        + "Setoid.lift_unique proves that agreement on all representatives "
                        + "determines this map uniquely.")),
                    Paragraph(Text(
                        "This closes exactly qdo-v1 theorem/30.3, atom "
                        + "qdo-residual-9cbd5454e4464eb527f9e996993dc72fdc5305d0ce8a4ad1"
                        + "fadeaaa429cec9be. "
                        + "No claim about canonical representatives or unrelated observer "
                        + "completion properties is included."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Kernel(Formula map) => Seq(Ker, Sp, map);

    private static Formula Quotient(Formula map) =>
        Seq(Operatorname, Grp(F.Id("Quotient")), Open, Kernel(map), Close);

    private static Formula RelativeIdentityFormula()
    {
        Formula fine = F.Id("fine");
        Formula coarse = F.Id("coarse");
        Formula forget = F.Id("forget");
        Formula descend = F.Id("descend");
        Formula x = F.Id("x");

        return Disp(Seq(
            Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Fine"), Comma, Sp,
            F.Id("Coarse"), Comma, Esc,
            fine, Colon, Sp, F.Id("X"), Sp, To, Sp, F.Id("Fine"), Comma, Sp,
            coarse, Colon, Sp, F.Id("X"), Sp, To, Sp, F.Id("Coarse"), Comma, Esc,
            forget, Colon, Sp, F.Id("Fine"), Sp, To, Sp, F.Id("Coarse"), Comma, Esc,
            coarse, Sp, Eq, Sp, forget, Sp, Circ, Sp, fine, Sp, Rightarrow, Esc,
            Kernel(fine), Sp, Subseteq, Sp, Kernel(coarse), Sp, Land, Esc,
            Exists, Bang, Sp, descend, Colon, Sp,
            Quotient(fine), Sp, To, Sp, Quotient(coarse), Comma, Esc,
            Call("Surjective", descend), Sp, Land, Sp,
            Forall, Sp, x, Comma, Sp,
            Apply(descend, Seq(OpenBracket, x, CloseBracket, Underscore, Grp(fine))),
            Sp, Eq, Sp, Seq(OpenBracket, x, CloseBracket, Underscore, Grp(coarse)), Dot));
    }
}

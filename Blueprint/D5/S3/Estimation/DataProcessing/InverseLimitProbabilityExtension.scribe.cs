using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class InverseLimitProbabilityExtensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A compatible family of finite joint probability laws has one unique Borel extension "
            + "on the corresponding finite tuple of inverse-limit threads.",
        H("Probability Extension on Compatible Threads"),
        Blocks(Describe.Lean(
            DescribeId.Create("unique-probability-extension"),
            DeclarationHandle.Create(
                "D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension."
                    + "exists_unique_probability_extension"),
            H("Compatible joint laws extend uniquely"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each alphabet is finite, nonempty, and discrete, with its Borel measurable "
                        + "structure. Adjacent carrier maps are surjective. At each level there "
                        + "is a probability law on tuples of the same fixed finite length.")),
                Paragraph(Text(
                    "The only compatibility condition on these laws is exact pushforward by "
                        + "the coordinatewise bonding map. No restricted feasible-law map is "
                        + "assumed surjective.")),
                Paragraph(Text(
                    "A prescribed symbol extends downward by the bonding maps and upward by "
                        + "chosen right inverses. These threads lift every finite joint law. "
                        + "The sets of completed probabilities with a prescribed level law "
                        + "are nonempty, closed, and decreasing. Compactness of the probability "
                        + "space gives their common member.")),
                Paragraph(Text(
                    "Two extensions have identical level laws, so the full event total-variation "
                        + "identity makes their distance zero. Equality on every measurable "
                        + "event establishes uniqueness.")),
                Paragraph(Text(
                    "Uniqueness concerns the extension of an already compatible family. It does "
                        + "not imply uniqueness of a nearest feasible law, and the theorem "
                        + "does not select compatible finite minimizers."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula l = F.Id("l");
        Formula n = F.Id("n");
        Formula mu = F.Id("mu");
        Formula family = F.Id("Q");
        Formula levelLaw = new Formula.Subscript(family, l);
        Formula nextLaw = new Formula.Subscript(family, Seq(l, Plus, D(1)));
        Formula bond = Call("nodewise", new Formula.Subscript(F.Id("q"), l), n);
        Formula projection = new Formula.Subscript(F.Id("pi"), l);
        return Disp(new Formula.Aligned([
            Seq(Open, Forall, Sp, l, Sp, InMacro, Sp, natural, Comma, Sp,
                Call("push", bond, nextLaw), Sp, Eq, Sp, levelLaw, Close, Sp, Rightarrow),
            Seq(Call("ExistsUnique", mu, Call("Prob", F.Id("X"))), Colon, Sp,
                Forall, Sp, l, Sp, InMacro, Sp, natural, Comma, Sp,
                Call("push", projection, mu), Sp, Eq, Sp, levelLaw),
        ]));
    }
}

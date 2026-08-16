using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class PrimeAdditiveGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every nonzero residue modulo a prime generates the additive group.",
        H("Additive Generators Modulo a Prime"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("every-nonzero-residue-modulo-a-prime-generates-the-additive-group"),
                DeclarationHandle.Create(
                    "D5/S3/ArithUnits/PrimeAdditiveGenerator.nonzero_generates_additive_group"),
                H("Every nonzero residue modulo a prime generates the additive group"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("p"), Sp, F.Text, Grp(F.Id("prime")), Comma, Quad, Sp,
                    Forall, Sp, F.Id("a"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("Z")), Slash, F.Id("p"), Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
                    F.Id("a"), Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("AddSubgroup"), Dot, F.Id("zmultiples")),
                    Open, F.Id("a"), Close,
                    Sp, Eq, Sp, Operatorname, Grp(F.Id("top"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural prime p and every nonzero residue a modulo p, the additive "
                        + "subgroup formed by all integer multiples of a is the full additive group "
                        + "ZMod p.")),
                    Paragraph(Text(
                        "This closes only the source clause saying that every nonzero element modulo "
                        + "a prime is a generator. The source atom's statements about deficits modulo "
                        + "twelve and its metamathematical discussion are not claimed here.")),
                    Paragraph(Text(
                        "Loogle and the pinned Mathlib source were searched before implementation. "
                        + "The exact general theorem zmultiples_eq_top_of_prime_card states that any "
                        + "nonzero element of a finite additive group of prime cardinality generates "
                        + "the whole group. The Lean proof applies it directly with ZMod.card, so no "
                        + "group-generation argument is re-proved."))),
                DescribeRole.Theorem
            ))));
}

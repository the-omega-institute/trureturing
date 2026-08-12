using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class CapacityMonotoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A genuine finite carrier merge lowers accessible capacity and cannot increase Shannon entropy.",
        H("Entropy and Capacity under Carrier Forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("accessible-capacity-is-carrier-cardinality"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/CapacityMonotone.accessibleCapacity"),
                H("Accessible capacity is carrier cardinality"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("capacity")), Open, F.Id("X"), Close,
                    Eq, Operatorname, Grp(F.Id("card")), Sp, F.Id("X"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Capacity is the independently specified number of accessible outcomes: " +
                        "for a finite carrier X it is Fintype.card X. It is deliberately not " +
                        "defined as a complement of Shannon entropy or KL divergence.")),
                    Paragraph(Text(
                        "This carrier-size quantity is the record-count side of forgetting. " +
                        "A later theorem can therefore compare capacities even when the input " +
                        "law changes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("deterministic-forgetting-lowers-entropy-and-capacity"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/CapacityMonotone.deterministic_forgetting_entropy_capacity_monotone"),
                H("Deterministic forgetting lowers entropy and capacity"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("f"), Underscore, Grp(Star), F.Id("p"), Close,
                    Leq, Sp, F.Id("H"), Open, F.Id("p"), Close, Sp, Land, RowBreak,
                    F.Id("H"), Open, F.Id("f"), Underscore, Grp(Star), F.Id("p"), Close,
                    Leq, Sp, Log, Sp, Operatorname, Grp(F.Id("capacity")), Open, F.Id("Y"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("capacity")), Open, F.Id("Y"), Close,
                    Leq, Sp, Operatorname, Grp(F.Id("capacity")), Open, F.Id("X"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative mass function on a finite carrier X. " +
                        "A surjective map f : X -> Y merges records deterministically; " +
                        "pushforward f p is the resulting law on Y. When the carrier-size " +
                        "hypothesis says Y is strictly smaller than X, the theorem proves " +
                        "H(pushforward f p) <= H(p), bounds the output entropy by " +
                        "log(card Y), while the surjection independently proves that the " +
                        "accessible carrier cannot be larger after forgetting. The strict " +
                        "capacity decrease is supplied as a genuine shrink hypothesis, not " +
                        "repeated as a conclusion.")),
                    Paragraph(Text(
                        "The entropy inequality is derived from the finite entropy chain rule " +
                        "applied to the graph-supported joint law of (f x, x). Its conditional " +
                        "entropy is nonnegative, while the first marginal is exactly the " +
                        "deterministic pushforward. The log-cardinality bound is the independent " +
                        "maximum-entropy theorem on the smaller output carrier.")),
                    Paragraph(Text(
                        "Surjectivity is used only for the carrier comparison; the entropy " +
                        "argument itself remains valid for any deterministic map. No equality " +
                        "criterion for injectivity on support is claimed here."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boolean-to-unit-merge-is-strict"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/CapacityMonotone.bool_unit_merge_strict_witness"),
                H("The Boolean-to-unit merge is strict"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("H"), Open, F.Id("f"), Underscore, Grp(Star), F.Id("u"), Close,
                    Lt, Sp, F.Id("H"), Open, F.Id("u"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("capacity")), Open, Operatorname, Grp(F.Id("Unit")), Close,
                    Lt, Sp, Operatorname, Grp(F.Id("capacity")), Open, Operatorname, Grp(F.Id("Bool")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The uniform Boolean law is pushed through the genuine merge Bool -> Unit. " +
                        "The output is the unique unit record, so its entropy is zero, while the " +
                        "input entropy is log 2.")),
                    Paragraph(Text(
                        "The same witness has accessible capacity 1 on Unit and 2 on Bool, with " +
                        "log 1 < log 2. It is therefore a concrete strict carrier-decrease and " +
                        "strict entropy-decrease example, rather than a restatement of an entropy " +
                        "deficit under a renamed capacity."))),
                DescribeRole.Theorem))));
}

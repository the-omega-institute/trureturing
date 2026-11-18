using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagCompletion;

internal sealed class SalinasSchmeisBoundedHeightLeastExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagCompletion/SalinasSchmeisBoundedHeightLeastExtension.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/salinasschmeis2026omega");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Least extensions at bounded finite height and the finite skeleton obstruction.",
        H("Least omega-chain extensions at bounded finite height"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partitionable-by"), DeclarationHandle.Create(Prefix + "PartitionableBy"),
                H("Parts of a prescribed inherited order type"),
                StatementSource.FromAuthor(Disp(PartitionFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The family consists of actual subsets. IsPartition demands nonempty parts, "
                    + "unique membership and whole-carrier coverage. Each part carries its induced "
                    + "order. For A equal to the natural numbers this is OmegaPartitionable. "
                    + "For A equal to the dual of the natural numbers this expresses an omega-star partition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-least-extension"), DeclarationHandle.Create(Prefix + "IsLeastExtension"),
                H("Leastness among partitionable extensions"),
                StatementSource.FromAuthor(Disp(LeastFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Both base maps are induced order embeddings. Comparison only asks for an order "
                    + "embedding of Q into X. There is no equation involving the two base maps. "
                    + "Every partial order on a carrier in universe w is eligible as X if it extends P "
                    + "and has the indicated partition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("has-least-extension"), DeclarationHandle.Create(Prefix + "HasLeastExtension"),
                H("Least candidates in independent universes"),
                StatementSource.FromAuthor(Disp(HasLeastFormula())), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The level u is for P, v is for the candidate and w is for comparisons. "
                    + "These levels are fixed independently. An order on Q is part of the witness. "
                    + "For the natural chain as A, taking this predicate for every P gives the "
                    + "telescope of the original question."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("least-ordinal-sum"),
                DeclarationHandle.Create(Prefix + "ordinalSum_isLeastExtension"),
                H("The ordinal sum as an explicit least extension"),
                StatementSource.FromAuthor(Disp(TopFormula(ordinalSum: true))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Reuse ordinalSumPartition for the actual sum U of P followed by the naturals. "
                        + "In a competing extension X, find the partition part containing the image "
                        + "of the greatest element t. Shift the natural enumeration of this part to "
                        + "start one step after the index of the image of t. The resulting strict tail "
                        + "lies strictly above every base image.")),
                    Paragraph(Text(
                        "On the left summand use the supplied base embedding, and on the right "
                        + "summand use the strict tail. Each map preserves and reflects comparisons "
                        + "within its summand. Every left image is below each right image, and "
                        + "antisymmetry forbids a comparison in the other direction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("least-with-top"),
                DeclarationHandle.Create(Prefix + "hasLeastOmegaExtension_of_top"),
                H("The greatest-element implication at every candidate level"),
                StatementSource.FromAuthor(Disp(TopFormula(ordinalSum: false))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A countable carrier has a Mathlib Shrink copy in the prescribed universe. "
                    + "orderIsoShrink transports the order. Transport each literal partition part "
                    + "by its image and compose its inherited order isomorphism. Surjectivity gives "
                    + "coverage, and injectivity gives uniqueness of parts from the original family. "
                    + "Compose the distinguished base embedding with the isomorphism and every "
                    + "comparison with its inverse. This argument needs no height bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("least-iff-greatest"),
                DeclarationHandle.Create(Prefix + "hasLeastOmegaExtension_iff"),
                H("The countable bounded-height classification"),
                StatementSource.FromAuthor(Disp(ClassificationFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The chain height is the supremum of the extended natural cardinalities of "
                        + "chains. A finite bound rules out every embedded increasing omega sequence "
                        + "and makes the greatest chain size attained. Applying well-foundedness of "
                        + "the reverse strict order to the upper set of each p gives a maximal "
                        + "point above p. If the maximal point were unique it would be greatest.")),
                    Paragraph(Text(
                        "Use the literal ordinal sum U and the literal maximal-ray extension V. "
                        + "Reuse ordinalSumPartition and maximalRayPartition with the chosen "
                        + "maximal-above assignment. Their countable carriers have actual "
                        + "order-isomorphic copies in the comparison universe. The construction "
                        + "allows countably infinitely many maximal points.")),
                    Paragraph(Text(
                        "Any least candidate embeds into both actual models by composing the "
                        + "comparison embeddings with the inverses of the chosen order isomorphisms. "
                        + "The image of a strict omega tail in U leaves P, stays in the natural "
                        + "summand and is cofinal there. Reflecting an upper bound built in such a "
                        + "tail proves that the candidate is upward directed. In V an omega tail "
                        + "also leaves P and reaches a ray over some m. The only upper bounds of "
                        + "that ray point are on the same ray. Directedness then puts every image "
                        + "point either below m in the base or on that ray.")),
                    Paragraph(Text(
                        "Compose the induced copy of P in the candidate with the embedding into V. "
                        + "Each maximal point of P has another incomparable maximal point. Every "
                        + "ray point and the base point m are comparable with every point in the "
                        + "concentrated image, so the images of the maximal points lie strictly "
                        + "below m. The same is true of all base images by maximal-above. Transport "
                        + "an attained h-element chain of P through this induced copy below m. "
                        + "Adjoining m yields h plus one elements in a chain of P.")),
                    Paragraph(Text(
                        "For a finite nonempty poset, the number of points bounds chain sizes. "
                        + "A nonempty countable antichain has height one and a greatest point "
                        + "exactly when it is a singleton. One bottom point below at least two "
                        + "incomparable maxima has height two and lacks a greatest point, including "
                        + "when the set of maxima is countably infinite.")),
                    Paragraph(Text(
                        "The empty poset is least using the empty partition and its unique "
                        + "embeddings. A singleton has a greatest point, so the two-point "
                        + "antichain has minimum counterexample cardinality. A nonempty finite "
                        + "chain embeds into the naturals by its increasing finite enumeration. "
                        + "Any admissible extension of that chain contains an actual partition "
                        + "part, which gives an embedding from the naturals. Thus the naturals "
                        + "are themselves a least extension of every nonempty finite chain.")),
                    Paragraph(Text(
                        "For the dual statement keep the same partition family and dualize its "
                        + "inherited isomorphisms. Dualize both ends of every base and comparison "
                        + "embedding. Each arbitrary comparison target can be dualized back, and "
                        + "dualizing twice restores the original data. Chain cardinalities are "
                        + "preserved. This gives the least-element classification for omega-star "
                        + "partitions, including finite, antichain, fork, finite-chain and empty "
                        + "cases. It also gives the reversed Rays and Tail obstruction, including "
                        + "the dual fork and the two-point antichain, and transports the "
                        + "lexicographic fiber construction for arbitrary base posets.")),
                    Paragraph(Text(
                        "The naturals have the single full part as an omega partition. The identity "
                        + "makes them an admissible self-extension, and every competing extension "
                        + "already admits an embedding of the naturals. Any n has a larger point "
                        + "n plus one, and the initial segments have unbounded finite sizes. "
                        + "The dual natural order is least for omega-star partitions and has no "
                        + "least element. These are boundary cases for the uniform height hypothesis.")),
                    Paragraph(Text(
                        "This is the bounded-height theorem and its applications in the revision-2 "
                        + "note by Haobo Ma (ChronoAI Pte Ltd, Singapore) and Wenlin Zhang (National "
                        + "University of Singapore and ChronoAI Pte Ltd, Singapore). The original "
                        + "Fork, Rays and Tail refutation and its settlement retain their credit. "
                        + "Remi Salinas Schmeis owns the posing question and the cited prior "
                        + "partition and lifting results."))),
                DescribeRole.Theorem),
            new DocumentBlock.Section(
                H("A cofinal inherited chain without a partition"),
                Blocks(
                    new DocumentBlock.DisplayFormula(Disp(FiniteSkeletonFormula())),
                    Paragraph(Text(
                        "For each natural n at least two, use the chain Fin(n+1) with its usual "
                        + "order. The strict interval above zero is the literal tail {1, …, n}, "
                        + "isomorphic to Fin(n) under successor. It contains the greatest point, "
                        + "so the one-member family consisting of this interval is pairwise "
                        + "disjoint with a cofinal union, as in Definition 2.33.")),
                    Paragraph(Text(
                        "In any proposed partition, each part has cardinality n by its inherited "
                        + "order isomorphism with Fin(n). Setoid.IsPartition.ncard_eq_finsum "
                        + "applied to the whole finite carrier gives the sum of the cardinalities "
                        + "of all parts. If there are m parts this gives n+1 = nm, so n divides 1. "
                        + "This contradicts n at least two.")),
                    Paragraph(Text(
                        "For n = 1, singleton parts partition every partial order. A one-point "
                        + "order has no inherited two-point chain and therefore no 2-skeleton. "
                        + "The finite obstruction is the second clause of the skeleton corollary "
                        + "in revision 2 by Haobo Ma and Wenlin Zhang. Its first clause, concerning "
                        + "extensions for every nonzero ordinal, is in the lexicographic fiber document.")))))));

    private static Formula FiniteSkeletonFormula()
    {
        var n = F.Id("n");
        var chain = Call("Fin", n);
        var larger = Call("Fin", Seq(n, Sp, Plus, Sp, D(1)));
        var tail = Call("Ioi", Seq(D(0), Sp, Colon, Sp, larger));
        return All("n", Seq(Mathbb, Grp(F.Id("N"))), Seq(
            D(2), Sp, Le, Sp, n, Sp, Rightarrow, RowBreak,
            Call("IsCofinal", tail), Sp, Land, Sp,
            Call("Nonempty", Call("OrderIso", chain, tail)), Sp, Land, RowBreak,
            Neg, Sp, Call("PartitionableBy", chain, larger)));
    }

    private static Formula PartitionFormula()
    {
        var a = F.Id("A");
        var p = F.Id("P");
        var d = F.Id("D");
        var c = F.Id("C");
        var parts = All("C", Call("Set", p), Seq(c, Sp, InMacro, Sp, d, Sp, Rightarrow, Sp,
            Call("Nonempty", Call("OrderIso", a, c))));
        var partition = Exists("D", Call("Set", Call("Set", p)),
            Seq(Call("IsPartition", d), Sp, Land, Sp, parts));
        return Carriers(Eqv(Call("PartitionableBy", a, p), partition), ("A", "a"), ("P", "u"));
    }

    private static Formula LeastFormula()
    {
        var a = F.Id("A");
        var p = F.Id("P");
        var q = F.Id("Q");
        var x = F.Id("X");
        var ord = F.Id("xOrder");
        return Carriers(Eqv(Call("IsLeastExtension", F.Id("w"), a, p, q), Seq(
            Call("IsExtension", p, q), Sp, Land, Sp, Call("PartitionableBy", a, q),
            Sp, Land, RowBreak,
            All("X", TypeAt("w"), All("xOrder", Call("PartialOrder", x), Seq(
                Call("IsExtension", p, x, ord), Sp, Rightarrow, Sp,
                Call("PartitionableBy", a, x, ord), Sp, Rightarrow, Sp,
                Call("Nonempty", Call("OrderEmbedding", q, x, ord))))))),
            ("A", "a"), ("P", "u"), ("Q", "v"));
    }

    private static Formula HasLeastFormula()
    {
        var a = F.Id("A");
        var p = F.Id("P");
        var q = F.Id("Q");
        return Carriers(Eqv(HasLeast(a, p),
            Exists("Q", TypeAt("v"), Exists("qOrder", Call("PartialOrder", q),
                Call("IsLeastExtension", F.Id("w"), a, p, q, F.Id("qOrder"))))),
            ("A", "a"), ("P", "u"));
    }

    private static Formula TopFormula(bool ordinalSum)
    {
        var p = F.Id("P");
        var t = F.Id("t");
        var claim = ordinalSum
            ? Call("IsLeastExtension", F.Id("w"), Naturals(), p, Call("OrdinalSum", p, Naturals()))
            : HasLeast(Naturals(), p);
        return Carriers(Seq(Instance("Countable", p), Sp,
            All("t", p, Seq(Call("IsTop", t), Sp, Rightarrow, Sp, claim))), ("P", "u"));
    }

    private static Formula ClassificationFormula()
    {
        var p = F.Id("P");
        var greatest = Exists("t", p, Call("IsTop", F.Id("t")));
        var classification = Eqv(HasLeast(Naturals(), p), Parenthesized(greatest));
        return Carriers(Seq(Instance("Nonempty", p), Sp, Instance("Countable", p), Sp,
            Call("chainHeight", Call("univ", p), Call("le", p)), Sp, Neq, Sp, Infty,
            Sp, Rightarrow, RowBreak, Parenthesized(classification)), ("P", "u"));
    }

    private static Formula Carriers(Formula body, params (string Name, string Level)[] carriers)
    {
        foreach (var (name, level) in carriers.Reverse())
        {
            body = All(name, TypeAt(level), Seq(Instance("PartialOrder", F.Id(name)), Sp, body));
        }
        return body;
    }

    private static Formula HasLeast(Formula a, Formula p) =>
        Call("HasLeastExtension", F.Id("v"), F.Id("w"), a, p);

    private static Formula Instance(string name, Formula carrier) =>
        Seq(OpenBracket, Call(name, carrier), CloseBracket);

    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);

    private static Formula Eqv(Formula left, Formula right) => Seq(left, Sp, Leftrightarrow, Sp, right);
    private static Formula TypeAt(string level) => Seq(F.Id("Type"), Sp, F.Id(level));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class CommutingCompletionExchangeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/CommutingCompletionExchange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The FourState countermodel realizes a discrete FLOW/FLOW/CUT kernel.",
        H("Commuting Completion Exchange Realization"),
        Blocks(
            Definition("commuting-completion-concrete-realization",
                "commutingCompletionRealization", "Concrete completion realization",
                "The primitive realization assigns the two source maps to the FLOW slots and the source predicate to the CUT slot."),
            Node("commutativity-necessary-realization",
                "commutativity_hypothesis_is_necessary_realization",
                "Countermodel realization equivalence",
                CertificateFormula(),
                "Unfolding identifies both negated source clauses with the realization law."),
            Node("commutativity-necessary-partition-count",
                "commutativity_hypothesis_is_necessary_partition_count",
                "Four kernel classes", PartitionCountFormula(),
                "Exhaustive FourState evaluation gives four distinct signatures."),
            Node("commutativity-necessary-private-pair",
                "commutativity_hypothesis_is_necessary_private_pair",
                "Private pair separation",
                AgreesFormula(),
                "The second flow sends a and b to different states."))));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);

    private static Formula CertificateFormula()
    {
        Formula firstOrder = Call("predictiveProjection", F.Id("counterexampleF"),
            Call("predictiveProjection", F.Id("counterexampleG"), F.Id("counterexampleReadout")));
        Formula secondOrder = Call("predictiveProjection", F.Id("counterexampleG"),
            Call("predictiveProjection", F.Id("counterexampleF"), F.Id("counterexampleReadout")));
        Formula statement = Seq(
            Neg, Sp, Call("Commute", F.Id("counterexampleF"), F.Id("counterexampleG")),
            Sp, Land, Sp, Neg, Sp, Call("KernelEquivalent", firstOrder, secondOrder));
        Formula law = Seq(F.Id("commutingCompletionArena"), Dot, F.Id("Law"),
            Open, F.Id("commutingCompletionRealization"), Close);
        return Seq(Grp(statement), Sp, Iff, Sp, law);
    }

    private static Formula PartitionCountFormula()
    {
        Formula state = F.Id("state");
        Formula carrier = F.Id("FourState");
        Formula signature = Seq(Open,
            Apply(F.Id("counterexampleF"), state), Comma, Sp,
            Apply(F.Id("counterexampleG"), state), Comma, Sp,
            Apply(F.Id("counterexampleReadout"), state), Close);
        Formula imageCard = Seq(Open, F.Id("Finset"), Dot, F.Id("univ"), Dot,
            F.Id("image"), Open, Lambda(Seq(state, Colon, Sp, carrier), signature), Close,
            Close, Dot, F.Id("card"));
        return Seq(imageCard, Sp, Eq, Sp, D(4));
    }

    private static Formula AgreesFormula()
    {
        Formula first = Seq(F.Id("FourState"), Dot, F.Id("a"));
        Formula second = Seq(F.Id("FourState"), Dot, F.Id("b"));
        return Seq(Neg, Sp, F.Id("commutingCompletionRealization"), Dot,
            F.Id("toPrimitiveBundle"), Dot, F.Id("agrees"), Open,
            first, Comma, Sp, second, Close);
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Sp, Mapsto, Sp, body, Close);
}

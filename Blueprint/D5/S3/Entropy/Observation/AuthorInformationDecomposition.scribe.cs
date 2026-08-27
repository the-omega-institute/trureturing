using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class AuthorInformationDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/AuthorInformationDecomposition."
            + "author_information_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional action entropy splits into internal-state information and residual entropy.",
        H("Author Information Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("author-information-decomposition"),
                DeclarationHandle.Create(Declaration),
                H("Internal-state information decomposes conditional action entropy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Public, Action, and Memory be arbitrary finite carriers. The "
                            + "nonnegative joint mass is ordered as Public times (Action times "
                            + "Memory), matching the conditioning coordinate used by the "
                            + "canonical finite entropy interface.")),
                    Paragraph(Text(
                        "The public-action law is the canonical projection that sums out "
                            + "Memory. The action-given-public-and-memory law is constructed by "
                            + "reindexing the same joint mass onto (Public times Memory) times "
                            + "Action; it is not defined from the target equality.")),
                    Paragraph(Text(
                        "Applying the entropy chain rule before and after that reindexing shows "
                            + "that action entropy given Public equals conditional mutual "
                            + "information between Action and Memory given Public, plus the "
                            + "action entropy remaining after Memory is also known.")),
                    Paragraph(Text(
                        "The two explanatory bullets following the source's boxed identity are "
                            + "interpretive labels for its summands, not additional mathematical "
                            + "clauses."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula publicType = F.Id("Public");
        Formula actionType = F.Id("Action");
        Formula memoryType = F.Id("Memory");
        Formula jointLaw = F.Id("jointLaw");
        Formula point = F.Id("z");
        Formula publicActionLaw = F.Id("actionGivenPublicLaw");
        Formula publicMemoryActionLaw = F.Id("actionGivenPublicMemoryLaw");
        Formula jointCarrier = Call(
            "Prod", publicType, Call("Prod", actionType, memoryType));
        Formula publicMemoryCarrier = Call("Prod", publicType, memoryType);
        Formula reindexedCarrier = Call("Prod", publicMemoryCarrier, actionType);
        Formula nonnegative = Seq(
            Forall, Sp, point, Colon, Sp, jointCarrier, Comma, Sp,
            D(0), Sp, Leq, Sp, Call("jointLaw", point));
        Formula reindexedValue = Call(
            "jointLaw",
            Call("pair", Call("fst", Call("fst", point)),
                Call("pair", Call("snd", point), Call("snd", Call("fst", point)))));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, publicType, Comma, Sp, actionType, Comma, Sp,
                memoryType, Colon, Sp, type, Comma),
            Seq(
                Open, Call("Fintype", publicType), Sp, Land, Sp,
                Call("Fintype", actionType), Sp, Land, Sp,
                Call("Fintype", memoryType), Close, Comma),
            Seq(
                jointLaw, Colon, Sp, jointCarrier, Sp, To, Sp, real, Comma, Sp,
                nonnegative, Sp, Rightarrow),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                publicActionLaw, Sp, Colon, Eq, Sp,
                Call("xyProjection", jointLaw), Comma),
            Seq(
                Operatorname, Grp(F.Id("let")), Sp,
                publicMemoryActionLaw, Colon, Sp,
                reindexedCarrier, Sp, To, Sp, real,
                Sp, Colon, Eq, Sp, point, Sp, Mapsto, Sp, reindexedValue, Comma),
            Seq(
                Call("conditionalEntropy", publicActionLaw), Sp, Eq, Sp,
                Call("conditionalMutualInformation", jointLaw), Sp, Plus, Sp,
                Call("conditionalEntropy", publicMemoryActionLaw), Dot),
        ]));
    }
}

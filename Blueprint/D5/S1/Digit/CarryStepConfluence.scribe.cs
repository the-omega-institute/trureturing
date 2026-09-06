using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class CarryStepConfluenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/CarryStepConfluence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Arbitrary raw Zeckendorf carry paths preserve value, select one canonical endpoint, and are globally confluent.",
        H("Confluence of Raw Zeckendorf Carries"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("raw-carry-paths-preserve-value"),
                DeclarationHandle.Create(Prefix + "rawValue_reflTransGen"),
                H("Raw value is invariant along every carry path"),
                StatementSource.FromAuthor(PathImplication(
                    Call("rawValue", F.Id("r")),
                    Call("rawValue", F.Id("s")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction over the reflexive-transitive closure composes the frozen one-step value law for each local carry."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalization-is-invariant-along-raw-carry-paths"),
                DeclarationHandle.Create(Prefix + "normalize_eq_of_reflTransGen"),
                H("Normalization is invariant along every carry path"),
                StatementSource.FromAuthor(PathImplication(
                    Call("normalize", F.Id("r")),
                    Call("normalize", F.Id("s")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both deterministic outputs are canonical and their raw values agree by pathwise preservation, so canonical uniqueness identifies them."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reachable-canonical-endpoint-is-normalize"),
                DeclarationHandle.Create(Prefix + "reachable_canonical_eq_normalize"),
                H("Every reachable canonical endpoint is the fixed normal form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), Comma, Sp, F.Id("s"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("RawDigits")), Comma, Sp,
                    Path(F.Id("r"), F.Id("s")), Sp, Land, Sp,
                    Call("CanonicalRaw", F.Id("s")), Sp, Rightarrow, Sp,
                    F.Id("s"), Sp, Eq, Sp, Call("normalize", F.Id("r")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Canonical inputs are fixed by normalization, while normalization invariance transports the endpoint back to the original source."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-carry-step-is-confluent"),
                DeclarationHandle.Create(Prefix + "carryStep_confluent"),
                H("The raw carry relation is globally confluent"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), Comma, Sp, F.Id("s"), Comma, Sp,
                    F.Id("t"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("RawDigits")), Comma, Sp,
                    Path(F.Id("r"), F.Id("s")), Sp, Land, Sp,
                    Path(F.Id("r"), F.Id("t")), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("u"), Sp, InMacro, Sp,
                    Operatorname, Grp(F.Id("RawDigits")), Comma, Sp,
                    Path(F.Id("s"), F.Id("u")), Sp, Land, Sp,
                    Path(F.Id("t"), F.Id("u")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Normalize both arms of an arbitrary peak. Path invariance identifies both deterministic normal forms, producing a common reduct without critical-pair enumeration.")),
                    Paragraph(Text(
                        "Pinned Mathlib and D5 searches found generic closure and Church-Rosser infrastructure, but no theorem for this raw carry relation. The result therefore reuses those interfaces and proves the domain-specific global property requested by the paper review."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/Normalize"))]));

    private static Formula Path(Formula source, Formula target) =>
        Call("ReflTransGen", F.Id("CarryStep"), source, target);

    private static Formula PathImplication(Formula left, Formula right) =>
        Disp(Seq(
            Forall, Sp, F.Id("r"), Comma, Sp, F.Id("s"), Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("RawDigits")), Comma, Sp,
            Path(F.Id("r"), F.Id("s")), Sp, Rightarrow, Sp,
            left, Sp, Eq, Sp, right, Dot));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}

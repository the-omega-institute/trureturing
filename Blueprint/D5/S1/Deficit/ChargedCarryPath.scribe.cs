using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class ChargedCarryPathDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Deficit/ChargedCarryPath.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Raw Zeckendorf carry paths have a path-independent signed charge with exact golden-phase behavior.",
        H("Charged Raw Carry Paths"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-golden-integer-charge-ledger"),
                DeclarationHandle.Create(Prefix + "betaDigits_sub_chargedCarryStep"),
                H("Each charged carry satisfies the GoldenInt ledger"),
                StatementSource.FromAuthor(ChargedLedger("ChargedCarryStep")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every labeled local carry from r to s with charge z, the expansion-face "
                        + "GoldenInt value of r minus that of s is intToGolden(z), the canonical "
                        + "integer embedding into GoldenInt. The proof "
                        + "checks all four constructors against phi squared equals phi plus one; the "
                        + "two exceptional bottom rules contribute plus one and minus one, while both "
                        + "internal rule families contribute zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-path-golden-integer-ledger"),
                DeclarationHandle.Create(Prefix + "betaDigits_sub_chargedReduces"),
                H("The one-step charge ledger telescopes along every path"),
                StatementSource.FromAuthor(ChargedLedger("ChargedReduces")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction on the charged reduction composes the constructor-level ledger. Thus "
                        + "the path's accumulated integer label is an independently checked semantic "
                        + "difference, rather than a charge defined retrospectively from its endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("charged-canonical-normal-form-uniqueness"),
                DeclarationHandle.Create(Prefix + "charged_normal_form_unique"),
                H("Canonical endpoints and total charges are simultaneously unique"),
                StatementSource.FromAuthor(ChargedNormalFormUnique()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any two charged reductions from the same raw input to canonical endpoints have "
                        + "equal endpoints and equal integer charges. Raw canonical uniqueness identifies each "
                        + "endpoint with the fixed normalizer output, while the telescoping GoldenInt "
                        + "ledger and injectivity of the integer coordinate identify the charges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("deterministic-normalization-has-charged-path"),
                DeclarationHandle.Create(Prefix + "charged_normalize_exists"),
                H("The deterministic normalizer realizes its signed carry count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("r"), Sp, InMacro, Sp, Operatorname,
                    Grp(F.Id("RawDigits")), Comma, Quad, Sp,
                    Call("ChargedReduces", F.Id("r"), Call("normalize", F.Id("r")),
                        Call("carrySignedCount", F.Id("r"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Following carryPass recursively produces a charged derivation to normalize(r). "
                        + "At every scheduler step its constructor label equals carrySign, so the "
                        + "accumulated path label is exactly the existing carrySignedCount recursion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("analytic-deficit-equals-beatty-deficit"),
                DeclarationHandle.Create(Prefix + "deficit_eq_beattyDeficit"),
                H("The analytic deficit is the integer Beatty coboundary"),
                StatementSource.FromAuthor(ForNaturalPair(Seq(
                    Call("deficit", V(1), V(2)), Sp, Eq, Sp,
                    Call("intToReal", Call("beattyDeficit", V(1), V(2)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Here intToReal is the canonical integer embedding into the reals. "
                        + "The public beta closed form concentrates each reading in the Zeckendorf "
                        + "displacement plus a linear golden-conjugate term. The linear terms cancel "
                        + "under addition, and the public displacement theorem converts the remaining "
                        + "integer expression to the golden Beatty shift coboundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-carry-count-equals-beatty-deficit"),
                DeclarationHandle.Create(Prefix + "carrySignedCount_eq_beattyDeficit"),
                H("The canonical-addend carry charge equals the Beatty deficit"),
                StatementSource.FromAuthor(ForNaturalPair(Seq(
                    Count(V(1), V(2)), Sp, Eq, Sp,
                    Call("beattyDeficit", V(1), V(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen deficit integer theorem identifies the analytic deficit with the "
                        + "scheduler's signed carry count. Combining it with the public deficit-Beatty "
                        + "identity and injectivity of the real integer cast gives an exact integer equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-carry-count-phase-classifier"),
                DeclarationHandle.Create(Prefix + "carrySignedCount_phase_classifier"),
                H("Golden phase thresholds classify the signed carry charge exactly"),
                StatementSource.FromAuthor(PhaseClassification()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every pair of natural inputs, the signed normalization charge is plus one "
                        + "exactly below the inverse-golden phase threshold, minus one exactly at or "
                        + "above the golden-ratio threshold, and zero exactly in the intervening "
                        + "half-open band. This transports the existing Beatty classifier to the "
                        + "actual raw normalization dynamics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("signed-carry-charge-fixed-modulus-nonlocality"),
                DeclarationHandle.Create(Prefix + "carryCharge_not_determined_by_fixed_modulus"),
                H("No fixed modulus determines the signed carry charge"),
                StatementSource.FromAuthor(ModulusNonlocality()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each natural modulus m at least two, there are two natural input pairs that "
                        + "agree coordinatewise modulo m but have different signed normalization charges. "
                        + "The existing density theorem supplies pairs with unequal analytic deficits, "
                        + "and the deficit integer theorem transfers that inequality to carrySignedCount."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Digit/CarryStepConfluence")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/Beatty/BetaBeattyClosedForms")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/FixedModulusNoncongruence")),
        ]));

    private static Formula ChargedLedger(string relation) => Disp(Seq(
        Forall, Sp, F.Id("r"), Comma, Sp, F.Id("s"), Sp, InMacro, Sp,
        Operatorname, Grp(F.Id("RawDigits")), Comma, Sp,
        F.Id("z"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
        Call(relation, F.Id("r"), F.Id("s"), F.Id("z")), Sp, Rightarrow, Sp,
        Call("betaDigits", F.Id("r")), Sp, Minus, Sp,
        Call("betaDigits", F.Id("s")), Sp, Eq, Sp,
        Call("intToGolden", F.Id("z")), Dot));

    private static Formula ChargedNormalFormUnique() => Disp(Seq(
        Forall, Sp, F.Id("r"), Comma, Sp, F.Id("s"), Comma, Sp, F.Id("t"), Sp,
        InMacro, Sp, Operatorname, Grp(F.Id("RawDigits")), Comma, Sp,
        F.Id("z"), Comma, Sp, F.Id("w"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Quad, Sp,
        Call("ChargedReduces", F.Id("r"), F.Id("s"), F.Id("z")), Sp, Land, Sp,
        Call("CanonicalRaw", F.Id("s")), Sp, Land, Sp,
        Call("ChargedReduces", F.Id("r"), F.Id("t"), F.Id("w")), Sp, Land, Sp,
        Call("CanonicalRaw", F.Id("t")), Sp, Rightarrow, Sp,
        F.Id("s"), Sp, Eq, Sp, F.Id("t"), Sp, Land, Sp,
        F.Id("z"), Sp, Eq, Sp, F.Id("w"), Dot));

    private static Formula ForNaturalPair(Formula conclusion) => Disp(Seq(
        Forall, Sp, V(1), Comma, Sp, V(2), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Quad, Sp, conclusion, Dot));

    private static Formula PhaseClassification() => ForNaturalPair(Seq(
        Count(V(1), V(2)), Sp, Eq, Sp, Plus, D(1), Sp, Leftrightarrow, Sp,
        Phase(V(1)), Sp, Plus, Sp, Phase(V(2)), Sp, Lt, Sp,
        Varphi, Caret, Grp(Minus, D(1)), Comma, Quad, Sp,
        Count(V(1), V(2)), Sp, Eq, Sp, Minus, D(1), Sp, Leftrightarrow, Sp,
        Varphi, Sp, Leq, Sp, Phase(V(1)), Sp, Plus, Sp, Phase(V(2)), Comma, Quad, Sp,
        Count(V(1), V(2)), Sp, Eq, Sp, D(0), Sp, Leftrightarrow, Sp,
        Varphi, Caret, Grp(Minus, D(1)), Sp, Leq, Sp,
        Phase(V(1)), Sp, Plus, Sp, Phase(V(2)), Sp, Lt, Sp, Varphi));

    private static Formula ModulusNonlocality() => Disp(Seq(
        Forall, Sp, F.Id("m"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
        F.Id("m"), Sp, Geq, Sp, D(2), Sp, Rightarrow, Quad, Sp,
        Exists, Sp, V(1), Comma, Sp, V(2), Comma, Sp, VP(1), Comma, Sp, VP(2), Sp,
        InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Quad, Sp,
        V(1), Sp, Equiv, Sp, VP(1), Sp, Open, Operatorname, Grp(F.Id("mod")),
        Sp, F.Id("m"), Close, Sp, Land, Sp,
        V(2), Sp, Equiv, Sp, VP(2), Sp, Open, Operatorname, Grp(F.Id("mod")),
        Sp, F.Id("m"), Close, Comma, Quad, Sp,
        Count(V(1), V(2)), Sp, Neq, Sp, Count(VP(1), VP(2)), Dot));

    private static Formula Count(Formula first, Formula second) =>
        Call("carrySignedCount", Seq(
            Call("toRaw", Call("Z", first)), Sp, Plus, Sp,
            Call("toRaw", Call("Z", second))));

    private static Formula Phase(Formula value) => Call("goldenPhase", value);

    private static Formula V(byte index) => Seq(F.Id("v"), Underscore, D(index));

    private static Formula VP(byte index) => Seq(F.Id("v"), Underscore, D(index), Apos);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}

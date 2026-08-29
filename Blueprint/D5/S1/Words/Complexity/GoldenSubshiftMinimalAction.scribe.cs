using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class GoldenSubshiftMinimalActionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward shifts act on every word subshift, their subtype orbits have the expected "
            + "ambient ranges, and the frozen golden orbit-closure result registers the "
            + "golden subshift as a minimal natural-number action.",
        H("The Minimal Forward-Shift Action on the Golden Subshift"),
        Blocks(
            Paragraph(Text(
                "For a one-sided word x, write X_x for its prefix-language subshift. The "
                + "ambient density theorem for X_g is already frozen. This node exposes the "
                + "iterated shift lemma needed by downstream imports, installs the natural-"
                + "number action on the subshift subtype, identifies its orbit after coercion "
                + "to the ambient sequence space, and transfers the frozen result through "
                + "Subtype.dense_iff to register the minimal-action instance.")),
            Describe.Lean(
                DescribeId.Create("iterated-shift-preserves-word-subshift"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftMinimalAction."
                        + "shift_mem_wordSubshift"),
                H("Every iterated forward shift remains in the word subshift"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("y"), Sp, InMacro, Sp, F.Id("X"), Underscore, F.Id("x"),
                    Sp, Rightarrow, Sp, Forall, Sp, F.Id("i"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    SigmaLower, Caret, Grp(F.Id("i")), Open, F.Id("y"), Close,
                    Sp, InMacro, Sp, F.Id("X"), Underscore, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "GoldenSubshiftMinimality keeps this general form private, and "
                    + "SubshiftTopology privately keeps only the special case where the "
                    + "member is the generating word itself. The zero case is the given "
                    + "membership, and the successor case uses the existing one-step shift "
                    + "invariance. Its role is reuse, not an additional mathematical "
                    + "strengthening."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("word-subshift-natural-number-action"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftMinimalAction."
                        + "shiftAddAction"),
                H("Forward shifts define a natural-number action on each word subshift"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("x"), Comma, Sp,
                    Operatorname, Grp(F.Id("AddAction")), Open,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("X"), Underscore, F.Id("x"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The action sends (i,y) to the subtype point represented by shift i y; "
                    + "the preceding theorem supplies its membership proof. "
                    + "FullShift.shift_zero and FullShift.shift_add supply the two action "
                    + "laws, the latter after commuting the two indices because mathlib "
                    + "states iterated shifts in the opposite composition order. Mathlib "
                    + "provides those laws for the ambient shift but does not install this "
                    + "action instance on the subshift subtype."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coerced-orbit-equals-forward-shift-range"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftMinimalAction."
                        + "coe_orbit_eq_range"),
                H("The coerced subtype orbit is the ambient forward-shift range"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("val")), Open,
                    Operatorname, Grp(F.Id("Orb")), Open,
                    Mathbb, Grp(F.Id("N")), Comma, Sp, F.Id("y"), Close, Close,
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("range")), Open, F.Id("i"), Sp,
                    Mapsto, Sp, SigmaLower, Caret, Grp(F.Id("i")), Open,
                    F.Id("y"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Unfolding the registered scalar action shows pointwise that coercing an "
                    + "orbit element gives the corresponding ambient forward shift. The two "
                    + "set inclusions then identify the image of the subtype orbit with the "
                    + "range indexed by natural shift times."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-subshift-minimal-action"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/GoldenSubshiftMinimalAction."
                        + "goldenSubshiftIsMinimal"),
                H("The golden subshift carries the minimal forward-shift action"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("IsMinimal")), Open,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("X"), Underscore, F.Id("g"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a point of the golden subshift subtype, coe_orbit_eq_range "
                    + "rewrites the coerced action orbit as its ambient forward-shift range. "
                    + "The frozen "
                    + "golden_wordSubshift_minimal theorem supplies the ambient closure "
                    + "equality. Subtype.dense_iff transfers that equality to density in the "
                    + "subtype, and this node records the result as the mathlib "
                    + "AddAction.IsMinimal instance."))),
                DescribeRole.Theorem))));
}

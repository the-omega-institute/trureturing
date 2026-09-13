using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.RawObservation;

internal sealed class NormalizationResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Identify exactly which coordinate normalization discards and which raw facts remain unrecoverable.",
        H("Normalization Charge and the Limits of Golden-State Recovery"),
        Blocks(
            Paragraph(Text(
                "The charge is the existing carrySignedCount of the actual normalizer. "
                + "The proof reuses the existing charged path existence and golden-difference "
                + "ledger; it does not attach a new hidden variable by definition. Write A(n) "
                + "for the first coordinate of the existing canonical object betaGolden(n).")),
            Describe.Lean(
                DescribeId.Create("raw-normalization-charge-spectrum"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/NormalizationResidual.charge_spectrum_iff"),
                H("The complete charge spectrum at a fixed display"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Charges"), Open, F.Id("n"), Close, Sp, Eq, Sp, OpenBrace,
                    F.Id("c"), Sp, Colon, Sp,
                    F.Id("A"), Open, F.Id("n"), Close, Sp, Plus, Sp, F.Id("c"),
                    Sp, Leq, Sp, F.Id("n"), Sp, Land, Sp,
                    F.Id("n"), Sp, Leq, Sp, D(2), Open,
                    F.Id("A"), Open, F.Id("n"), Close, Sp, Plus, Sp, F.Id("c"),
                    Close, CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalizer ledger identifies betaDigits(r).a with A(rawValue(r)) "
                    + "plus carrySignedCount(r). Substitution into the exact image theorem "
                    + "gives necessity. Its constructive converse realizes every allowed "
                    + "charge with an actual raw input; no attainable charge is omitted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-normalization-shift-defect"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/NormalizationResidual.normalization_shift_defect"),
                H("The discarded coordinate reappears with its exact Fibonacci multiplier"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("shiftValue"), Open, F.Id("k"), Comma, F.Id("r"), Close,
                    Sp, Minus, Sp,
                    F.Id("shiftValue"), Open, F.Id("k"), Comma,
                    F.Id("normalize"), Open, F.Id("r"), Close, Close,
                    Sp, Eq, Sp, F.Id("Fib"), Open, F.Id("k"), Close,
                    F.Id("charge"), Open, F.Id("r"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The equality is in the integers, so signed charges are retained. "
                    + "Multiply the actual golden normalization defect by phi^k and take "
                    + "its second coordinate. The existing phi-power Fibonacci identity "
                    + "gives the coefficient. In particular all shifts survive normalization "
                    + "exactly when its charge is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-equal-shifts-different-carry-guards"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/NormalizationResidual.all_shifts_hide_carry_applicability"),
                H("Equal complete shift observations can hide an available carry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("SameAllShiftsDifferentCanonicality"), Open, F.Id("i"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every i, one input has a single token at i+2; the other has one token "
                    + "at i and one at i+1. The actual charged adjacent rule has zero charge, "
                    + "so their golden images and every shifted integer display agree. "
                    + "The single token is canonical; the adjacent pair is not and has "
                    + "a real CarryStep to the single-token input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("raw-canonicality-no-shift-decoder"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/RawObservation/NormalizationResidual.no_shift_only_canonicality_test"),
                H("Even the entire shift sequence cannot decide canonicality"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("ShiftOnlyCanonicalityDecoder"), Sp, Rightarrow, Sp, F.Id("False")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A predicate of the full shift sequence must agree on equal sequences. "
                    + "The explicit adjacent-carry pair gives opposite canonicality values, "
                    + "so no such predicate can represent canonicality on all raw inputs. "
                    + "This is a semantic obstruction, not a claim about computation time. "
                    + "It does not by itself settle a stochastic Zeckendorf game, whose "
                    + "transition relation and probability law require separate identification."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/RawObservation/ShiftReadout")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Deficit/ChargedCarryPath")),
        ]));
}

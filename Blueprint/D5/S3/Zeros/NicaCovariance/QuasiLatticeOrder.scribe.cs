using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.NicaCovariance;

internal sealed class QuasiLatticeOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic shift realizes the full divisibility quasi-lattice: lcm joins multiply "
        + "range projections, while gcd meets control quotients and cross-commutation.",
        H("Quasi-Lattice Order and Nica Covariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("range-projections-multiply-at-the-lcm-join"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "shift_range_projection_comp"),
                H("Range projections multiply at the lcm join"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("shiftRangeProjection")), Open,
                    Operatorname, Grp(F.Id("tableSup")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The encoding of tableSup u v is the least common multiple of the two "
                    + "address encodings. A coefficient survives both range projections exactly "
                    + "when its address is divisible by this lcm, so their product is the single "
                    + "projection at the join. Symmetry of lcm also makes the family commute."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-join-recovers-normalized-table-addition"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "tableSup_eq_normalizedTableAdd_of_coprime"),
                H("A coprime join recovers normalized table addition"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Coprime")), Open,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close, Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("v"), Close, Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("tableSup")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("normalizedTableAdd")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coprimality identifies the lcm with the product, while normalized table "
                    + "addition encodes that same product. This theorem is the in-module bridge "
                    + "showing that the frozen coprime projection and double-commutation results "
                    + "are specializations of the full quasi-lattice relations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("divisible-subspaces-meet-at-the-lcm-join"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "divisibleSubspace_inf"),
                H("Divisible subspaces meet at the lcm join"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close, Sp,
                    Operatorname, Grp(F.Id("inf")), Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")), Open,
                    Operatorname, Grp(F.Id("tableSup")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Membership in the submodule meet requires support on multiples of both "
                    + "addresses. Divisibility by tableSup u v is equivalent to those two "
                    + "conditions simultaneously, so the meet of the support subspaces is the "
                    + "support subspace at the lcm join."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("subspace-inclusion-is-reverse-address-divisibility"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "divisibleSubspace_le_iff"),
                H("Subspace inclusion is reverse address divisibility"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("u"), Close, Sp, Le, Sp,
                    Operatorname, Grp(F.Id("divisibleSubspace")),
                    Open, F.Id("v"), Close, Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("v"), Close, Sp, Mid, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")),
                    Open, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If v divides u, every multiple of u is a multiple of v, giving the reverse "
                    + "inclusion of divisible support subspaces. Conversely, the unit vector at "
                    + "u lies in divisibleSubspace u; applying an assumed inclusion forces u to "
                    + "pass the v-divisibility filter."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotients-by-the-gcd-meet-are-coprime"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "coprime_quotients"),
                H("Quotients by the gcd meet are coprime"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("Coprime")), Open,
                    Operatorname, Grp(F.Id("primeAxisEncoding")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("u"), Comma, Sp,
                    Operatorname, Grp(F.Id("tableInf")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close, Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("primeAxisEncoding")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("v"), Comma, Sp,
                    Operatorname, Grp(F.Id("tableInf")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close, Close,
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The encoding of tableInf u v is the gcd of the two address encodings. "
                    + "Factoring this common divisor from both addresses and cancelling its "
                    + "positive natural value leaves quotient encodings whose gcd is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("general-backward-forward-cross-commutation"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "backward_shift_comp_forward_translation"),
                H("Backward and forward shifts cross-commute through the meet"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("backwardShiftCLM")),
                    Open, F.Id("u"), Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("v"), Comma, Sp,
                    Operatorname, Grp(F.Id("tableInf")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close, Close,
                    Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("backwardShiftCLM")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("u"), Comma, Sp,
                    Operatorname, Grp(F.Id("tableInf")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close, Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write d for the gcd meet and factor u and v as quotient addresses times d. "
                    + "The quotient encodings are coprime, so the coordinate calculation reduces "
                    + "to coprime cross-commutation after cancelling d. Thus B_u V_v equals "
                    + "V_{v/d} B_{u/d} without a coprimality hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nica-cross-commutation-in-adjoint-form"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/NicaCovariance/QuasiLatticeOrder."
                    + "adjoint_forward_translation_comp"),
                H("Nica cross-commutation in adjoint form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), InMacro, Sp,
                    Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc,
                    Operatorname, Grp(F.Id("adjoint")), Open,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("u"), Close, Close, Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")),
                    Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("v"), Comma, Sp,
                    Operatorname, Grp(F.Id("tableInf")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close, Close,
                    Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("adjoint")), Open,
                    Operatorname, Grp(F.Id("forwardTranslationCLM")), Open,
                    Operatorname, Grp(F.Id("normalizedTableSub")),
                    Open, F.Id("u"), Comma, Sp,
                    Operatorname, Grp(F.Id("tableInf")),
                    Open, F.Id("u"), Comma, Sp, F.Id("v"), Close, Close, Close,
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Hilbert adjoint of forward translation is the corresponding backward "
                    + "shift. Rewriting both backward shifts in the general cross-commutation "
                    + "identity therefore gives the standard adjoint presentation of Nica "
                    + "covariance through the gcd meet."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/NicaCovariance/SemigroupRelations")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/NicaCovariance/DoubleCommutation")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/BackwardShiftAdjoint")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Zeros/ShiftOperators/ShiftRangeProjection")),
        ]));
}

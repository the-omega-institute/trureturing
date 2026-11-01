using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SectorChannels;

internal sealed class WordScaleTowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SectorChannels/WordScaleTower.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common digit words give a strictly composable compact physical CPTP tower.",
        H("Compact Physical Word Tower"),
        Blocks(
            Paragraph(Text("This construction is the physical transport part of the integer-scale sector tower. The intended base range b(s) >= 2 and finite nonempty sector families is included. Repeated bases, singleton families, level zero and zero-length segments require no exceptions. The local map acts on every physical matrix, including unused code coordinates and cross-sector coherences.")),
            Paragraph(Text("The proof first reconstructs a compact coordinate from its kept word and residual word. It then proves that equality of a direct residual word is equivalent to equality of the two consecutive residual words. Applying the actual Kraus action on every matrix unit yields full channel composition. Equality only on the encoded logical subspace is never used to infer equality on the physical matrix algebra.")),
            Describe.Lean(
                DescribeId.Create("compact-level"),
                DeclarationHandle.Create(Prefix + "Level"),
                H("Compact physical level"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The physical carrier at level n is the dependent sum of Fin(b(s)^n), retaining every sector label."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common-alphabet"),
                DeclarationHandle.Create(Prefix + "alphabet"),
                H("One common digit alphabet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The alphabet size is the maximum of the finite base family. Each sector digit embeds by its ordinary value."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common-word"),
                DeclarationHandle.Create(Prefix + "Word"),
                H("Common residual words"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A word of length l is a function from Fin l into the common finite alphabet. Empty words form a singleton."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compact-digits"),
                DeclarationHandle.Create(Prefix + "digits"),
                H("Least significant digits"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit pinned Mathlib finFunctionFinEquiv gives a genuine equivalence between Fin(b(s)^n) and length-n base-b(s) digit words. Its inverse evaluates the sum of digit(q) times b(s)^q."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("common-expansion"),
                DeclarationHandle.Create(Prefix + "commonWord"),
                H("Expansion in the common alphabet"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each sector digit is included in the same alphabet, without identifying the numerical values of whole residual integers across different bases."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("kept-word"),
                DeclarationHandle.Create(Prefix + "keep"),
                H("Retain the low positions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Restrict the actual compact basis word to positions below j, then use the same explicit base expansion equivalence to return to the compact level-j carrier."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residual-tail"),
                DeclarationHandle.Create(Prefix + "tail"),
                H("Discard the high positions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The residual word records the original positions j through n-1 in the fixed common alphabet. The same word equality compares residual digits across all sectors."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-word-kraus"),
                DeclarationHandle.Create(Prefix + "localKraus"),
                H("Actual word Kraus operators"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The matrix entry is one exactly when its retained coordinate and residual word match the input expansion, and zero otherwise. A common word invalid in a sector therefore annihilates every basis vector of that sector."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-word-channel"),
                DeclarationHandle.Create(Prefix + "localChannel"),
                H("Local CPTP channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Keep and tail together determine each compact input coordinate. This injectivity proves Kraus completeness. The existing finite_kraus_quantum_channel theorem then constructs the actual completely positive trace-preserving map."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("product-word-channel"),
                DeclarationHandle.Create(Prefix + "jointChannel"),
                H("Product physical channel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The joint channel uses pairs of independent residual-word labels. Its all-matrix tensor action is proved against the existing TensorRealization predicate."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strict-physical-tower"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Strict compact physical word tower"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite sector family, every base family and every n >= j >= h >= 0, the constructed local and joint channels compose strictly on their entire physical matrix algebras. The theorem also supplies their tensor realization, the exact local matrix-unit action and both zero-segment identity actions."))), DescribeRole.Theorem),
            Paragraph(Text("Original theorem 34.3 is not closed by this physical transport result. The common canonical level encoding, its exact encoded Schur action and reference lift, transfer of the published full operation-class optimum, the floor-lambda distinct-base limit, and both actual endpoint marginal bridges remain separate obligations. No standalone endpoint-normalization unit is supplied here."))
        )));
}

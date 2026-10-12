using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.Unitary;

internal sealed class PartIIUnitaryRadicalTraceCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual part iiunitary radical trace coordinates supplies the parameterized matrix, finite-field or ordered-product identities consumed by the whole-SU K5 width and intrinsic prescribed-product proof paths. All original hypotheses and actual carriers are retained; this source provides no oracle for bare automorphism recognition.",
        H("Part IIUnitary Radical Trace Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicaltracecoordinates-actual-radical-unitary-of-trace"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTraceCoordinates.actual_radical_unitary_of_trace"),
                H("actual radical unitary of trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal coordinate unitary criterion for the constructed radical. The column relation and corner trace are exactly those of the TRUE Steinberg inverse action; no unitary-recognition premise is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-partiiunitaryradicaltracecoordinates-actual-unitary-radical-row-lift"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Unitary/PartIIUnitaryRadicalTraceCoordinates.actual_unitary_radical_row_lift"),
                H("actual unitary radical row lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every genuine first-row quotient parameter has an ACTUAL unitary radical lift. The corner is constructed by surjective relative trace, including characteristic two and arbitrary ranks."))),
                DescribeRole.Theorem),
            Paragraph(Text("The results concern special-unitary matrix groups over finite fields. Their geometric setting is Nikolov and Segal, On finitely generated profinite groups, II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239. Prescribed-product statements retain their field-size, rank and automorphism hypotheses.")))));
}

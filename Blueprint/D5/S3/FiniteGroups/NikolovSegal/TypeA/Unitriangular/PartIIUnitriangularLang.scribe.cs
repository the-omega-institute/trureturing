using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularLangDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual arbitrary-field unitriangular Lang construction on Uplus n F. The height torus is restricted from the determinant-one matrix action, the finite inverse is a strict-upper Neumann sum, and the resonance obstruction is an explicit transvection.",
        H("Part II Unitriangular Lang"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-nonresonant"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.Nonresonant"),
                H("Nonresonant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root-weight condition quantifies over every positive distance below n and retains the arbitrary field and all rank-zero and rank-one cases."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-finite-solution-equation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_equation"),
                H("finite solution equation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit finite sum solves the strict-upper nonlinear coordinate equation by layer raising and the pinned geometric telescoping identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-finite-solution-unique"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLangLinear.finiteSolution_unique"),
                H("finite solution unique"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under nonresonance, every strict-upper solution of the coordinate equation equals the displayed finite Neumann sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-psi-lang-inverse"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.psi_langInverse"),
                H("psi Lang inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual Uplus subgroup, the explicit inverse is a right inverse for the orientation heightTorus a g multiplied by g inverse."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-lang-inverse-psi"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.langInverse_psi"),
                H("Lang inverse psi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same explicit construction is a left inverse on the actual Uplus subgroup, using strict-upper uniqueness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-resonant-transvection"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.resonant_transvection_not_range"),
                H("resonant transvection obstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When a positive root weight vanishes, the explicit transvection at that root is outside the range; the obstruction uses the actual matrix entry and no cardinality assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-unitriangular-lang-height-torus-criterion"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularLang.heightTorus_lang_criterion"),
                H("height torus Lang criterion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the actual Uplus subgroup over any field and every natural rank, surjectivity and bijectivity coincide and are equivalent to nonresonance."))),
                DescribeRole.Theorem),
            Paragraph(Text("The source keeps the determinant-one matrix carrier, the Uplus subgroup, the height torus and the strict-upper filtration explicit. It does not assume finite cardinality, algebraic closure, characteristic restrictions, or an opaque existence-only inverse.")))));
}

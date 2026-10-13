using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class FiniteHeckeArrayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite q-expansion arrays transport the project's actual prime Hecke operator to the first Miller coordinates.",
        H("Finite Hecke coefficient arrays"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-coefficient-array-apply"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.finiteCoefficientArray_apply"),
                H("Finite coefficient array"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "finiteCoefficientArray f N is the coefficient table indexed by Fin (N+1), so index i stores the actual analytic q-expansion coefficient a(f,i). The table includes the constant term and every coefficient through q^N."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("prime-hecke-finite-coordinate"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeFiniteCoordinate_eq"),
                H("Prime Hecke coordinate from finite precision"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p and i in Fin m, the coefficient a(T_p f,i+1) is exactly read from the source array of length p*m+1: use entry p*(i+1), and, when p divides i+1, add p^(k-1) times entry (i+1)/p. The proof rewrites the existing actual analytic coefficient law; the array indices are proved to lie below p*m+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-first-coefficients-array"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHecke_first_coefficients_from_array"),
                H("The first m Hecke coefficients use only q^(p*m)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first m nonconstant coefficients of T_p f are therefore determined by the finite source table through q^(p*m), equivalently by truncation modulo q^(p*m+1). For p=2 this is the 2*m+1 precision required by the T_2 matrix route."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-miller-matrix-basis"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHeckeMillerMatrix_apply_basis"),
                H("Finite Hecke entries on the Miller basis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Using the constructed integral Miller basis and its coefficient equivalence, each entry of primeHeckeMillerMatrix is the first-coordinate value of the project's actual analytic T_p applied to the corresponding Miller form. This is a complex matrix transport statement; integer-entry and characteristic-polynomial integrality remain subsequent obligations."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The module does not define a substitute coefficient operator and does not claim a Maeda result. It only packages the existing analytic Hecke law into a finite, executable index interface suitable for the next integer matrix and characteristic-polynomial step.")))));
}

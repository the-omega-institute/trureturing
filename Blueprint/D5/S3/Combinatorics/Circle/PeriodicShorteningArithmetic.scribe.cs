using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class PeriodicShorteningArithmeticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-phase charges across the three moduli",
        H("Same-phase charges across the three moduli"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodic-geom-sum"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_sum"),
                H("Geometric quotient as the shared finite sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The geometric quotient is bound to the existing GeometricSourceRelocation.geometric_quotient. The subsequent multiplication and recurrence calculations consume this equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-geom-mul"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mul"),
                H("The geometric multiplication identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The shared finite geometric sum gives (q-1)*G_r=q^r-1. The cross-modulus range proof and final strict-span calculation consume it."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-geom-succ"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_succ"),
                H("The geometric block recurrence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Appending the last geometric summand gives G_(r+1)=G_r+q^r. Charged block joins and the final source equation consume this recurrence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-geom-mono"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.geom_mono"),
                H("Monotone geometric block heights"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>=1, the geometric quotients increase with the block count. The physical candidate range and all early-block strips consume this order bound."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodic-source-equations"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/PeriodicShorteningArithmetic.periodic_source_equations"),
                H("Same-phase charges across the three moduli"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For d>=2, w<=2^(d-1)-1 and m>=2, set q=2^d, G=G_m and f(r,i)=2^i*w*G_r+e(i). The original physical value at exponent r*d+i+1 is exactly 2*G*a(i)-f(r,i); at the last block it is R*y(i+1)+H*a(i). The phase i is shared by a, y, e and f. Every e is nonnegative and its total is w; each block correction has total w*q^r. The label zero retains value w*G. No unit, injectivity of values or least-period premise is used.")),
                    Paragraph(Text("The charge is obtained from the binary prefix quotient of w. Centered uniqueness identifies the actual sources after both range and modular equality are proved. To certify every original block, the proof writes its candidate as q^r*y+K*a with K=2G-G_r-2q^r>=0, using both smaller centered ranges on the same phase. ZeroSumSubsets.source_cycle supplies the existing base total; the geometric quotient is reused at its original owner.")),
                    Paragraph(Text("This is a repository derivation of the conditional periodic-shortening construction. The source problem is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, Conjecture 3.1. No literature novelty or solution of its general aperiodic case is asserted."))),
                DescribeRole.Theorem)), []));
}

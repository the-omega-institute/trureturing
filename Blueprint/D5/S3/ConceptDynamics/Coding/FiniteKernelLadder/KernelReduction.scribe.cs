using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FiniteKernelLadder;

internal sealed class KernelReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual kernel quotients and original-power invariants",
        H("Actual kernel quotients and original-power invariants"),
        Blocks(
            Paragraph(Text("Actual COLUMN linear maps induce quotient dynamics over each kernel. Finite coordinates, lag stabilization and the cumulative quotient maps connect successive quotients to powers on the original carrier.")),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder/KernelReduction.quotientBasis"),
                H("Generic quotient maps and finite coordinates"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any commutative ring L and L-modules V,W with additive commutative group structures, KQuot f is V/ker(f), project f is the actual quotient map, factor f is its lift with codomain W, and factor f composed with project f equals f. reduced T is project T composed with factor T on V/ker(T). The square for r:V to W and s:W to V uses the extra center V/ker(r), together with the actual quotients by ker(s.comp r) and ker(r.comp s).")),
                    Paragraph(Text("The displayed quotientBasis construction further requires IsDomain L and IsPrincipalIdealRing L, and a finite basis bW indexed by Fin n of the codomain W. It constructs a finite basis of V/ker(f) from a PID basis of range(f) through quotKerEquivRange. An input basis for V is unnecessary here. The domain, quotient and range may be zero, and f need not be injective.")),
                    Paragraph(Text("The dyadic specialization constructs its domain and PID instances using localization of the integers and extension of contracted ideals. Its finite bases are actual data, not an assumed freeness field. These are applications of quotient and PID library constructions, not separate escape content."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder/KernelReduction.kernel_square"),
                H("Four RS triangles with both vertical terms"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over GyrationDyadic, with arbitrary finite bases at the original two modules, the center and both kernel quotients, kernel_square retains value(original r,s)+value(target project,factor)=value(source project,factor)+value(bottomForward,bottomBackward). The period d is nonzero and divisible by three. Any chosen dimensions, including zero, and singular r,s and dynamics are allowed.")),
                    Paragraph(Text("The four value_triangle applications consume the actual quotient factorization equations. Each square vertex uses the same basis in every incident triangle. In particular both vertical terms remain in the statement; naturality of a commutative square or an asserted open-edge basis invariance cannot replace these four RS triangles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder/KernelReduction.unitFromLag"),
                H("Kernel stabilization and an actual inverse from lag"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The lag algebra is over an arbitrary commutative ring and arbitrary additive commutative group modules; no finite-rank or PID hypothesis enters it. Let a be an actual endomorphism unit on V, B an endomorphism on W, f:V to W, g:W to V and k any natural number, with g.comp f=a^k, f.comp g=B^k and g.comp B=a.comp g. The two lag products make f injective and g surjective, and identify ker(B^k)=ker(g). The intertwiner gives ker(B^(k+q))=ker(B^k) for every natural q.")),
                    Paragraph(Text("powerQuotientEnd is the actual induced dynamics on W/ker(B^k), and its injectivity follows from those equations. When B itself has been made injective, unitFromLag proves g bijective and conjugates a through that actual equivalence to construct a two-sided inverse for B. B is not inverted in the kernel argument. Injectivity over the dyadic PID alone never supplies a unit; the actual lag equations are essential."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-4"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder/KernelReduction.q_zero_iff"),
                H("Successive kernel quotients remove exactly the original power kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A Based object stores a finite free dyadic module, its actual basis, dimension and arbitrary endomorphism T. It has no unit or injectivity field. reduce quotients by the kernel of the current stage endomorphism; it does not put a new power on the original module. The quotient basis is chosen once per vertex, using the actual transported original basis in the injective branch and the dyadic range construction otherwise.")),
                    Paragraph(Text("For every Based X, natural stage j and original vector x, q_zero_iff states X.q j x=0 iff (X.time^j)x=0. Here X.q j is the composite of the j actual successive quotient projections into the recursively changed carrier. Induction uses the one-step quotient zero test and the actual q_intertwines equation. Thus ker(q^j)=ker(T^j) on the original carrier, with no eventual-kernel premise. The all-stage connection across these actual quotient carriers is a substantive candidate beyond the one-step quotient identity."))),
                DescribeRole.Theorem))));
}

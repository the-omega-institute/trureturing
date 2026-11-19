using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RealRogFailureQuantitativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original cone base norm attains its primal minimum with the original strictly positive unit.",
        H("Primal attainment on the original cone"),
        Blocks(
            Paragraph(Text("For the primal optimization in Quantum Origin VI, the original-carrier theorem retains the arbitrary strictly positive original unit, the entire compact base and the generating cone. Full-support compression, determinant normalization, a same-object saturating dual effect, extraction from an actual failed local antipodal pair, purity transport and the return to the original carrier remain open. Primal attainment alone does not complete Proposition 93.3 or supply block classification, Jordan structure, self-duality or a zero-gluing premise.")),
            Describe.Lean(DescribeId.Create("mass-cap-compact"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/RealRogFailureQuantitative.mass_cap_compact"),
                H("The whole original mass cap is compact"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any real normed carrier, pointed cone C and strictly positive original unit u, compactness of the entire normalized base implies compactness of every full cap {x in C : u(x)<=R} for nonnegative R. The zero vector and empty-base case are retained. The original primal theorem and UnitPreservingLiftImage.minimum_lift and closed_lift_image consume this original statement."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-primal-attainment"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/RealRogFailureQuantitative.original_primal_attainment"),
                H("An attained primal on the original cone with its original unit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let A be an arbitrary finite-dimensional real normed vector space, C a pointed cone whose real span is all of A, and u the same real linear functional throughout. Assume u is strictly positive on every nonzero point of C and the entire base C intersect {u=1} is compact. For every z in A, there exist X,Y in C with z=X-Y and u(X)+u(Y) equal to BaseNormContraction.baseNorm for this C,u,z. The same X,Y minimize the original mass cost over every feasible pair in C. Their masses are respectively (baseNorm(z)+u(z))/2 and (baseNorm(z)-u(z))/2. In particular u(z)=0 forces equal masses on this actual optimum; no change of unit or matrix representation occurs.")),
                    Paragraph(Text("The compactness step identifies the entire mass cap {a in C : u(a)<=R} with [0,R] times the original base with zero adjoined, including the zero vector and empty-base case. The product of two such compact caps, intersected with the closed original difference fiber X-Y=z, is compact and contains an initial feasible decomposition supplied by PointedCone.mem_span. A continuous mass minimum on this fiber is a global minimum: every lower-cost feasible pair lies in both caps, and every pair outside the cost bound has larger cost. IsLeast.csInf_eq then identifies this actual minimum with the existing source-defined base norm. The mass-cap parametrization supplies the compactness needed for the minimizing fiber.")),
                    Paragraph(Text("This proves the primal portion used in (93.12) and (93.23), on the whole original carrier and without trace normalization, ROG or a zero-gluing assumption. It does not produce a dual functional, prove base-norm polarity or the failed-pair bound 0<baseNorm(p-r)<2, or establish saturation by a common proper effect. Those obligations cannot be inferred from attainment alone. The cone base-norm definition is reused from BaseNormContraction; finite-dimensional continuity and compact minimization are pinned Mathlib inputs. The mass-cap and global-minimum argument implements the source's compactness proof in 90.9; no literature-priority claim is made."))), DescribeRole.Theorem),
            Paragraph(Text("The base-norm definition and nonnegativity of the original unit on the cone are reused directly from BaseNormContraction. The base and the normalized nonzero cone-point membership theorem are reused directly from CircuitBalancedConfirmation.base and CircuitBalancedConfirmation.normalized_mem. Finite-dimensional continuity, compact scalar-set multiplication, compact minimization and IsLeast.csInf_eq are pinned Mathlib inputs. The mass-cap parametrization and global-minimum argument implement the compactness proof in 90.9; no literature-priority claim is made.")))));
}

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FiniteKernelLadderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual kernel towers and exact endpoint coordinates",
        H("Actual kernel towers and exact endpoint coordinates"),
        Blocks(
            Paragraph(Text("An actual finite path of COLUMN elementary equivalences induces a path on the simultaneous vertex quotients constructed by KernelReduction. The ROW matrix rows(bV,bW,f) is literally transpose(toMatrix(bV,bW,f)), so rows(g.comp f)=rows(f)*rows(g). Forward rows therefore multiply in chronological order.")),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-5"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder.strip"),
                H("The complete dependent finite strip"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any Path X Y n, nonzero d divisible by three, strip states w.weight d+Y.vertical=X.vertical+w.reduce.weight d. Edges store actual COLUMN maps r,s with s.comp r=X.time and r.comp s=Y.time. Each Edge.reduce is constructed on the two actual vertex quotients, and Edge.cell applies the four-triangle kernel square.")),
                    Paragraph(Text("Induction cancels every interior vertical contribution because the module and stored basis are literally shared by its two incident cells. No endpoint or intermediate invertibility is needed for strip. Only afterwards, for unit endpoints, the transported endpoint bases identify project with I and factor with the original time; the existing identity-edge weight then removes the two boundary values. The same cochain and actual letters remain throughout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-6"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder.final_all_isUnit"),
                H("Finite termination at the original path length"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any Path w from X to Y of original length n and IsUnit X.time, every vertex time of w.stage n is a unit. Each original vertex has an actual prefix of length k at most n. RectangularNilpotenceBarrier.exchange_chain_lag supplies the existing coupled witnesses for that prefix; faithful row coordinates produce the actual COLUMN lag maps. lag_kernel_after and ker(q^j)=ker(T^j) then make the stage-n vertex injective.")),
                    Paragraph(Text("The stage-n path still has its actual prefixes from its unit start. Those lag maps and unitFromLag construct the final units from the injective times. There is no guessed rank drop, bound by dimension, field-of-fractions shortcut or inference from injectivity over a PID to surjectivity. Original singular and zero-dimensional intermediates, and n=0, remain included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-7"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder.endpoint_basis_transport"),
                H("The full stored endpoint Sigma identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every unit endpoint X and every natural j, (X.stage j).coordinates equals the Sigma pair of X.dim and X.basis mapped by X.qEquiv h j. This identifies both the stored rank and the actual stored basis with the image under the same cumulative quotient equivalence q^j. Existence of some basis or equality of ranks alone is insufficient.")),
                    Paragraph(Text("Induction transports the entire Sigma through the next actual quotient projection, using the injective branch of quotientCoordinates. The same identity gives the original time matrix at the final endpoint, literal equality of the reconstructed unit vertex, and preservation of chronological forward rows. HEq transports the proved rank equality rather than supplying an unrelated basis-change premise. This stored-coordinate invariant is a substantive candidate distinct from finite PID freeness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finitekernelladder-8"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FiniteKernelLadder.arbitrary_loop_one_edge"),
                H("Return the actual unit word at the literal original endpoint"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Given only w : Path X X n and IsUnit X.time, the construction returns v on the literal original unit vertex and a row unit U whose value is w.forwardRows. It retains v.forward=w.forwardRows, commutation of U with X.matrix, and for every nonzero d divisible by three both v.weight d=w.weight d and w.weight d=dyadicGyration d w.forwardRows (U inverse*X.matrix).")),
                    Paragraph(Text("final_all_isUnit constructs the unit proof at each vertex of the stage-n path. unitWord reconstructs the existing finite unit-word type only at that stage; endpoint_unitVertex transports it back to the literal original vertex. stage_forwardRows fixes the actual product, strip fixes the same sum, and UnitWordGyration.Word.loop_one_edge gives the terminal expression. No BuiltLadder, quotient-basis, cochain-law or intermediate-unit hypothesis is added to the input."))),
                DescribeRole.Theorem),
            Paragraph(Text("For any loop w : Path X X k with unit X.time and any basis c of X.V indexed by Fin m, the full coordinate-transport application returns a genuine endomorphism unit a with a=w.forward and Commute a X.time. Set T=X.time, b=X.basis, s=T*a inverse in COLUMN order and C=rows(b,c,LinearMap.id). The output contains rows(b,b,a)*C=C*rows(c,c,a) and rows(b,b,s)*C=C*rows(c,c,s), together with s.comp a=T and a.comp s=T. The basis c is arbitrary; rectangular change-of-index matrices and zero ranks remain allowed.")),
            Paragraph(Text("For every natural d with NeZero d and three dividing d, the full boundary equation is w.weight d+value(b,c,LinearMap.id,T)=value(b,c,LinearMap.id,T)+value(c,c,a,s). It then gives w.weight d=value(c,c,a,s) by cancellation. The same RS two-triangle basis-change square supplies both equal endpoint terms because sr=rs=X.time. It asserts no invariance of an individual open-edge value. The ROW backward factor is row(a inverse)*row(X.time), obtained by transposing COLUMN X.time*a inverse.")),
            Paragraph(Text("For an actual endomorphism unit a and endomorphism T with Commute a T, Mathlib Commute.units_inv_left gives T*a inverse=a inverse*T. Both unit inverse identities and that commutation equation justify the order change. This equation is applied locally when converting the two-factor transport between COLUMN and ROW conventions.")),
            Paragraph(Text("UnitWordGyration.Word.collapse_weight, KernelReduction's Based.q_zero_iff, Path.strip, arbitrary_loop_one_edge and Based.endpoint_basis_transport connect the quotient construction to the complete finite word. The coupled all-word lag is the cumulative proof shared by FixedPositivePartitionSseDistance.theorem32_2 and Path.lag through RectangularNilpotenceBarrier.exchange_chain_lag. Quotient, coordinate and PID constructions supply the maps and bases used by these statements.")),
            Paragraph(Text("No strongest original-h statement, its h/Word/U/j/window k/s/Q parameters, either actual factor, p2/p7 and joint mod-three corrections, FixT6 or minimum6 premise is changed by this finite algebraic construction. No bounded calibration wrapper is supplied. Classical quotient, finite PID and RS-triangle methods are reused; no literature novelty is asserted.")),
            Paragraph(Text("The strongest original-h root, its finite calibrations, literal FixT6 and minimum6 are outside these finite algebraic statements. Their separate periodic and beam dictionaries and final acceptance obligations are required to close that original goal.")))));
}

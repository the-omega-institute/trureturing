using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class ActualHigherInventoryCoercivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete higher loss controls the full weighted inventory symmetric difference.",
        H("Coercivity of the complete higher inventory"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-higher-inventory-complete-coercivity"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/ActualHigherInventoryCoercivity.actual_complete_higher_inventory_coercivity"),
                H("A bound on every missing and excess higher coordinate"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real X >= exp(2) and every natural n >= 1, "
                        + "R is exactly actualDefect(X,n)-completeFirstLayerLoss(X,n). "
                        + "The theorem proves both nonnegativity of R and the displayed bound. "
                        + "higherInventoryMismatch sums log(p) over the full symmetric difference "
                        + "of coordinates(n) and coordinates(strictInteger(referencePrice(X))). "
                        + "Here coordinates(n) contains every (p,j) with p prime and "
                        + "2 <= j <= factorization(n,p), and referencePrice(X)=1/(X log X). "
                        + "Missing and excess coordinates contribute positively before summation; "
                        + "this is stronger information than the absolute signed difference "
                        + "of the two aggregate higher masses.")),
                    Paragraph(Text("The pointwise_inventory_l1 inequality "
                        + "keeps the occupied Boolean, the strict central threshold and both "
                        + "neighbouring strict thresholds. It includes zero weights and threshold "
                        + "ties. finite_inventory_l1 sums these coordinate losses on an arbitrary "
                        + "finite support, including the empty support, before cancellation can "
                        + "occur. actual_inventory_dual_estimate uses the union of the entire "
                        + "actual inventory and the low-price canonical inventory. The latter "
                        + "bounds canonical occupancy only; it places no cap on actual support "
                        + "or on any exponent.")),
                    Paragraph(Text("CompleteHigherInventoryDuality.literal_loss_identity "
                        + "identifies the finite dual loss with this same R. Its canonical "
                        + "coordinate monotonicity supplies the central and neighbouring canonical "
                        + "sets. ActualHigherMassResponse.actual_higher_mass_response supplies "
                        + "the existing two-price response bound. From ActualHigherMassCoercivity, "
                        + "the proof reuses actual_complete_higher_mass_coercivity only for "
                        + "nonnegativity of R, and balance_response for the final optimization "
                        + "with q=sqrt(X) and L=log(X). The pointwise and finite inequalities, "
                        + "rather than the old signed mass estimate, control the full mismatch.")),
                    Paragraph(Text("The existing epsilon branch of balance_response handles "
                        + "R=0 while retaining the logarithmic boundary remainder. Zero loss "
                        + "does not unconditionally imply zero mismatch: strict-threshold ties "
                        + "remain possible. The unit n=1, valuations zero and one, all higher "
                        + "layers and arbitrary prime support remain in the theorem's domain. "
                        + "No record, PNT estimate or support cap is assumed. This repository "
                        + "composition asserts no paper novelty, prescribed-bank payment, "
                        + "signed B(P) bound, Robin inequality beyond 5040 or proof of RH."))),
                DescribeRole.Theorem))));
}

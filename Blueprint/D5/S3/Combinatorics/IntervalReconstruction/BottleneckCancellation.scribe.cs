using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.IntervalReconstruction;

internal sealed class BottleneckCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prescribed deletion of k occurrence pairs increases a bottleneck matching bound to (k+1) epsilon + k eta.",
        H("Quantitative cancellation of occurrence matchings"),
        Blocks(Describe.Lean(DescribeId.Create("bottleneck-occurrence-cancellation"),
            DeclarationHandle.Create("D5/S3/Combinatorics/IntervalReconstruction/BottleneckCancellation.result"),
            H("One complement bijection with a simultaneous error bound"),
            StatementSource.FromLean(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("M is an arbitrary pseudometric space. X and Y index actual "
                    + "occurrences, and a:X→M and b:Y→M give their labels. The equivalence "
                    + "e:X≃Y pairs every occurrence with distance at most epsilon. Finite "
                    + "subsets U and V specify the occurrences to delete, and d:U≃V pairs "
                    + "these deleted occurrences with distance at most eta. Both error bounds "
                    + "hold on the same a and b. The nonnegative real numbers epsilon and eta "
                    + "need not be equal. Write k=card(U). There exists one total equivalence "
                    + "f:(X\\U)≃(Y\\V) for which every retained pair has distance at most "
                    + "(k+1)epsilon+k eta. The equivalence f works for all retained occurrences "
                    + "simultaneously.")),
                Paragraph(Text("No compatibility between e and d is imposed. Labels can repeat, "
                    + "distinct labels can have zero distance, and M can be infinite. Empty "
                    + "index sets, zero deletions and deletion of every occurrence are included; "
                    + "an empty M is allowed whenever the label maps exist. In fact X and Y "
                    + "may also be infinite: the construction only requires U and V to be finite. "
                    + "Consequently no independent cardinality equality or finiteness hypothesis "
                    + "on Y is needed. The supplied equivalences carry the required cardinal "
                    + "information. The integer k counts deleted occurrences, including those "
                    + "whose labels coincide.")),
                Paragraph(Text("The reusable proof is Omega.BottleneckCancellation.complement_bound "
                    + "in OmegaMath.Combinatorics.BottleneckCancellation. This D5 declaration is "
                    + "a direct book citation, classified bind-only; its mathematical content "
                    + "belongs to that general proof. The proof first allows a separate nonnegative "
                    + "budget c(x) for each original matching edge and w(i) for each deleted "
                    + "pair p(i),q(i). It constructs a complement equivalence whose edge at x "
                    + "has distance at most c(x)+sum_i(c(p(i))+w(i)).")),
                Paragraph(Text("For one deleted pair p(i),q(i), let z=e⁻¹(q(i)). Swapping p(i) "
                    + "and z in the source makes the new matching send p(i) to q(i), so these "
                    + "two occurrences can be removed from the ambient types. Only the edge "
                    + "starting at z changes. Its new distance is bounded by the old budget "
                    + "c(z) plus c(p(i))+w(i), using three edges and the pseudometric triangle "
                    + "inequality. Induction handles the remaining deletion pairs. Injectivity "
                    + "of their occurrence indexing and the fact that x is retained ensure that "
                    + "the exceptional budget is charged at most once among x and the remaining "
                    + "deleted sources. The weighted estimate therefore adds each deleted "
                    + "budget once. Substituting c(x)=epsilon and w(i)=eta gives the stated "
                    + "constant.")),
                Paragraph(Text("For noisy interval reconstruction, X and Y would index full "
                    + "endpoint-pair observations; U and V would be the actual observations "
                    + "wholly inside the known prefixes. Thus k is the number of those "
                    + "endpoint-pair occurrences, rather than the prefix length. The existing "
                    + "exact reconstruction uses multiset cancellation in "
                    + "Omega.MonotoneIntervalReconstruction.prefix_extension. Applying the "
                    + "quantitative theorem additionally requires an eta estimate for actual "
                    + "prefix observations, an occurrence correspondence with the residual "
                    + "multisets, and quantitative extension estimates. Those conclusions are "
                    + "not supplied here. This is a general mathematical cancellation estimate, "
                    + "with no assertion of full noisy recovery, optimal constants, computational "
                    + "complexity or resolution of general Turnpike."))),
            DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativePresburgerDescriptorObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No finite uniform native Nat Presburger descriptor interface exactly reads all native alpha replies.",
        H("All Native Trees: Uniform Presburger Descriptor Obstruction"),
        Blocks(
            Paragraph(Text(
                "Source is the original FreeMagma Bool carrier of all finite native trees; "
                + "Address is the physical List Bool carrier. Original readout distinguishes "
                + "alpha, beta, branch and absent. The claim concerns exact alpha replies "
                + "at epoch zero for every finite source and every physical address.")),
            Describe.Lean(
                DescribeId.Create("full-native-presburger-interface-claim"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction.claim"),
                H("The full existential interface"),
                StatementSource.FromAuthor(Disp(Call("Exists", F.Id("finiteUniformInterface")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exist finite types K and T, dimensions r:K->Nat and q:T->Nat, "
                    + "arbitrary predicates admitted(k,x) on Nat^r(k) and valid(t,y) on "
                    + "Nat^q(t), and maps Theta from admitted tuples to actual Source "
                    + "and Real from valid descriptors to physical addresses. Theta "
                    + "covers every Source and Real covers every Address. For each k,t "
                    + "there is one arbitrary native presburger.Formula on "
                    + "Fin(r(k)+(q(t)+1)), including any quantifier nesting. Its free "
                    + "valuation is Fin.append x.val (Fin.cons 0 y.val): source coordinates "
                    + "first, then epoch zero, then descriptor coordinates. For every "
                    + "admitted x and valid y and every a related by Real(t,y,a), formula "
                    + "truth is equivalent to readout(a,Theta(k,x))=alpha. Subtypes encode "
                    + "admission and validity, without additional positivity, inhabitance, "
                    + "injectivity, definability or bounded-tree assumptions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("full-native-presburger-interface-refutation"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePresburgerDescriptorObstruction.result"),
                H("The full claim is false"),
                StatementSource.FromAuthor(Disp(Call("Not", F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "NatPresburger.compile_correct transfers native Nat realization "
                        + "to the original integer Formula.holds. The actual empty Fin 0 "
                        + "bound vector is default, matching native Formula.Realize. "
                        + "The environment's reversed bound prefix is empty. The exact "
                        + "Fin.append/Fin.cons correspondence gives ofFn(Int.ofNat x) "
                        + "followed by 0::ofFn(Int.ofNat y), preserving source-prefix "
                        + "length r(k). Formula.holds_iff_quantifierEliminate transfers "
                        + "both ways to the original QE output, so arbitrary natural "
                        + "quantifiers retain all compiler nonnegative guards.")),
                    Paragraph(Text(
                        "Apply PresburgerFormulaGrowth.qf_growth to each QE output, "
                        + "using admitted source and valid descriptor subtypes. Its "
                        + "actual f,C,s,Growth data are passed to the existing live "
                        + "NativePolynomialDescriptorObstruction.growth_obstruction. "
                        + "That proof chooses distinct equal-depth physical addresses "
                        + "and covering descriptors before a pattern, fills one common "
                        + "finite native tree with its alpha/beta leaves, and uses arbitrary "
                        + "source-chart coverage and all-realization exactness to realize "
                        + "all 2^n patterns. A finite exponential value exceeds the fixed "
                        + "finite-family polynomial bound, giving the contradiction.")),
                    Paragraph(Text(
                        "The compiled result is literally Not claim, with no universe "
                        + "parameters on the closed utility pair. Interface and the live "
                        + "obstruction proof allow arbitrary tag universes. Any finite "
                        + "K,T reindex to Fin(card(K)),Fin(card(T)) through Fintype.equivFin: "
                        + "pull back r,q,admitted,valid,Theta,Real,reply along the inverse "
                        + "equivalences; their surjectivity transfers both coverage laws "
                        + "and exactness is unchanged. Thus the closed claim loses no "
                        + "finite tag family. Empty K or T and "
                        + "zero numeric dimensions remain in its quantifiers; coverage "
                        + "itself rules out empty tags for an actual interface. An "
                        + "all-epoch exact interface would imply this epoch-zero claim "
                        + "and is therefore refuted by the same application. This says "
                        + "nothing about native undecidability, a concrete controller, "
                        + "restricted source families, or conditional UDB synthesis. "
                        + "The exact obstruction is a repository application of the "
                        + "supplier compiler/QE and the native joint-pattern result; "
                        + "it claims no new general Presburger tameness theorem."))),
                DescribeRole.Theorem))));
}

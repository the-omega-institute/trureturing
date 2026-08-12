using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ConditionalEntropyEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vanishing finite conditional entropy in nats characterizes point-mass conditional laws exactly on nonzero-marginal slices.",
        H("Equality at the Lower Endpoint of Conditional Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("point-mass-conditionals-on-support-force-zero-entropy"),
                DeclarationHandle.Create("D5/S3/Entropy/ConditionalEntropyEquality.conditional_entropy_eq_zero_of_point_mass_on_support"),
                H("Point-mass conditionals on the marginal support force zero entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Forall, Sp, F.Id("i"), Comma, Sp,
                                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                                    Open, F.Id("i"), Close, Neq, Sp, D(0), Sp, Rightarrow, Sp, RowBreak,
                                    Exists, Sp, F.Id("j"), Comma, Sp,
                                    Operatorname, Grp(F.Id("conditional")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("i"), Close, Eq,
                                    Open, F.Id("k"), Mapsto, Sp,
                                    Begin, Grp(F.Id("cases")),
                                    D(1), Comma, Amp, F.Id("k"), Eq, F.Id("j"), RowBreak,
                                    D(0), Comma, Amp, F.Id("k"), Neq, Sp, F.Id("j"),
                                    End, Grp(F.Id("cases")), Close,
                                    Close, Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("conditionalEntropy")),
                                    Open, F.Id("p"), Close, Eq, D(0), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The support qualification is the central content of the statement. " +
                                        "It does not assert a conditional point mass, or a functional " +
                                        "dependence, on every slice. By definition, conditional p i j is " +
                                        "p(i,j) / marginal p i, hence it is the artificial quotient 0/0 when " +
                                        "marginal p i = 0. Such a slice contributes 0 times the Shannon entropy " +
                                        "of that arbitrary, generally non-normalized conditional function, " +
                                        "which is 0 regardless of the function. Vanishing conditional entropy " +
                                        "therefore says nothing about " +
                                        "zero-marginal slices; only slices carrying mass occur in the " +
                                        "characterization.")),
                                    Paragraph(Text(
                                        "A global function formulation would be false, not merely weaker. Take " +
                                        "iota inhabited, kappa empty, and p identically zero. Every marginal " +
                                        "vanishes, conditional entropy is zero, and the support-qualified " +
                                        "condition holds vacuously, but no function from iota to kappa exists. " +
                                        "Assuming Nonempty kappa would repair only the existence of an arbitrary " +
                                        "function; it would import an unrelated hypothesis and would still " +
                                        "suggest a dependence on zero-mass slices that the theorem does not " +
                                        "establish.")),
                                    Paragraph(Text(
                                        "This direction needs no nonnegativity hypothesis. On a mass-carrying " +
                                        "slice, the displayed equality identifies the entire conditional " +
                                        "function with a point mass, so the frozen " +
                                        "entropy_eq_zero_iff_point_mass theorem gives zero slice entropy " +
                                        "directly. On a zero-marginal slice, the outer marginal factor makes the " +
                                        "summand vanish. The conclusion follows by summing these zero terms.")),
                                    Paragraph(Text(
                                        "The equality of functions is stronger and more informative than the " +
                                        "claim that some conditional value equals 1. It records at once that the " +
                                        "selected value is 1 and every other value is 0; the weaker phrasing " +
                                        "would hide the latter part of the proved statement."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("zero-conditional-entropy-forces-point-masses-on-support"),
                DeclarationHandle.Create("D5/S3/Entropy/ConditionalEntropyEquality.point_mass_on_support_of_conditional_entropy_eq_zero"),
                H("Zero conditional entropy forces point masses on the marginal support"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open,
                                    F.Id("i"), Comma, Sp, F.Id("j"), Close,
                                    Close, Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("conditionalEntropy")),
                                    Open, F.Id("p"), Close, Eq, D(0), Sp, Rightarrow, RowBreak,
                                    Forall, Sp, F.Id("i"), Comma, Sp,
                                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                                    Open, F.Id("i"), Close, Neq, Sp, D(0), Sp, Rightarrow, Sp, RowBreak,
                                    Exists, Sp, F.Id("j"), Comma, Sp,
                                    Operatorname, Grp(F.Id("conditional")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("i"), Close, Eq,
                                    Open, F.Id("k"), Mapsto, Sp,
                                    Begin, Grp(F.Id("cases")),
                                    D(1), Comma, Amp, F.Id("k"), Eq, F.Id("j"), RowBreak,
                                    D(0), Comma, Amp, F.Id("k"), Neq, Sp, F.Id("j"),
                                    End, Grp(F.Id("cases")), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The converse requires pointwise nonnegativity. It makes every marginal " +
                                        "nonnegative and, on a slice with nonzero marginal, makes the conditional " +
                                        "function nonnegative. That slice is normalized directly from the " +
                                        "definitions: summing p(i,j) / marginal p i over j gives marginal p i / " +
                                        "marginal p i = 1. The last equality is valid exactly under the " +
                                        "nonzero-marginal premise.")),
                                    Paragraph(Text(
                                        "Consequently every marginal-weighted slice entropy is nonnegative. If " +
                                        "their finite sum, conditionalEntropy p, vanishes, the vanishing-sum " +
                                        "criterion forces each summand to vanish. On a mass-carrying slice, " +
                                        "mul_eq_zero and the nonzero marginal isolate zero Shannon entropy for " +
                                        "the conditional law. The frozen entropy_eq_zero_iff_point_mass theorem " +
                                        "then converts that equality into the displayed point-mass function.")),
                                    Paragraph(Text(
                                        "The right-hand side is not automatic from nonnegativity. For the " +
                                        "constant law 1/2 on Unit times Bool, pointwise nonnegativity holds and " +
                                        "the single marginal is 1, but the conditional law assigns 1/2 to both " +
                                        "Boolean values. It is uniform rather than a point mass, so the " +
                                        "support-qualified conclusion fails. This counterexample has been " +
                                        "compiled and checked independently.")),
                                    Paragraph(Text(
                                        "The conclusion remains deliberately silent on zero-marginal slices. " +
                                        "Their summands vanish before the slice entropy can be constrained, so " +
                                        "the converse supplies no additional dependence there."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("zero-conditional-entropy-iff-point-masses-on-support"),
                DeclarationHandle.Create("D5/S3/Entropy/ConditionalEntropyEquality.conditional_entropy_eq_zero_iff_point_mass_on_support"),
                H("Zero conditional entropy characterizes point masses on the marginal support"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open,
                                    F.Id("i"), Comma, Sp, F.Id("j"), Close,
                                    Close, Sp, Rightarrow, RowBreak,
                                    Open,
                                    Operatorname, Grp(F.Id("conditionalEntropy")),
                                    Open, F.Id("p"), Close, Eq, D(0), Sp, Leftrightarrow, Sp, RowBreak,
                                    Forall, Sp, F.Id("i"), Comma, Sp,
                                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                                    Open, F.Id("i"), Close, Neq, Sp, D(0), Sp, Rightarrow, Sp, RowBreak,
                                    Exists, Sp, F.Id("j"), Comma, Sp,
                                    Operatorname, Grp(F.Id("conditional")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("i"), Close, Eq,
                                    Open, F.Id("k"), Mapsto, Sp,
                                    Begin, Grp(F.Id("cases")),
                                    D(1), Comma, Amp, F.Id("k"), Eq, F.Id("j"), RowBreak,
                                    D(0), Comma, Amp, F.Id("k"), Neq, Sp, F.Id("j"),
                                    End, Grp(F.Id("cases")), Close,
                                    Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The three declarations are retained because the two implications have " +
                                        "different honest hypothesis sets. Point-mass conditionals imply zero " +
                                        "conditional entropy without nonnegativity, whereas the reverse " +
                                        "implication needs nonnegativity to turn the total into a sum of " +
                                        "nonnegative terms and infer that each term vanishes. Inflating the " +
                                        "first implication with hp merely to package the equivalence would " +
                                        "weaken that result for no mathematical reason.")),
                                    Paragraph(Text(
                                        "This equivalence characterizes the lower endpoint of the conditional-" +
                                        "entropy line in the bucket. It matches the lower-endpoint work for the " +
                                        "finite entropy bracket deposited in wave 23, and reuses that wave's " +
                                        "frozen entropy_eq_zero_iff_point_mass theorem as the slice-level tool. " +
                                        "The units are nats because shannonEntropy uses Real.log.")),
                                    Paragraph(Text(
                                        "The result is qualitative and finite. It makes no claim about " +
                                        "conditional mutual information, gives no continuous or measure-" +
                                        "theoretic analogue, and provides no rate, stability theorem, or deficit " +
                                        "estimate near the lower endpoint."))),
                DescribeRole.Theorem
            ))));
}

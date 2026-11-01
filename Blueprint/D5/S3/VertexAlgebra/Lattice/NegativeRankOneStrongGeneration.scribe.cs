using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class NegativeRankOneStrongGenerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/NegativeRankOneStrongGeneration.";
    private static Formula Datum() => Call("datum", F.Id("d"));
    private static Formula Carrier() => Call("Carrier", Datum());

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite family of arbitrary actual states has a proper negative-word span in negative rank one.",
        H("Negative Rank One Has No Finite Strong Generating Family"),
        Blocks(
            Paragraph(Text("For an integer d, datum(d) is the actual even LatticeData of rank one with Gram entry -2d. "
                + "The charge charge(d,s) is the constant function Fin(1) to Z with value s. The actual bilinear "
                + "form is B(s,t)=-2dst, chargeEnergy(s)=-ds^2, and a charge-s oscillator monomial of oscillator "
                + "energy r has energy r-ds^2. The carrier is the full finite-support charge direct sum of "
                + "complex oscillator polynomials, with the original all-state map LatticeAllStateField.Y.")),
            Paragraph(Text("For a finite set S of arbitrary actual states, negativeWord(D,S) evaluates every finite "
                + "list of pairs (a,n), with a in S and n a natural number: W([])=vacuum and "
                + "W((a,n)::w)=Y(a)_(-n-1) W(w), using normalized coefficients. negativeWordSpan is the "
                + "complex linear span of this entire range, including the empty word. StronglyGenerates(D,S) "
                + "means exactly that this subspace equals the whole actual carrier. This specifies the "
                + "right-nested convention. Word length, negative mode order, oscillator degree and the "
                + "finite charge mixtures in S are unrestricted.")),
            Describe.Lean(
                DescribeId.Create("negative-rankone-no-finite-strong-generation"),
                DeclarationHandle.Create(Prefix + "negative_rank_one_no_finite_strong_generation"),
                H("Every finite arbitrary-state family has a proper negative-word span"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("d"), InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Sp,
                    D(0), Lt, F.Id("d"), Rightarrow, Sp,
                    Forall, Sp, F.Id("S"), InMacro, Sp, Call("Finset", Carrier()), Comma, Sp,
                    Neg, Sp, Call("StronglyGenerates", Datum(), F.Id("S"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let M be the maximum absolute charge in the union of the finite charge "
                        + "supports of S, with maximum zero for an empty union. Linearity of the original Y "
                        + "expands every mixed state into its actual charge-homogeneous components. Enlarge "
                        + "the labels to all single(charge(d,s),p) with -M<=s<=M and arbitrary oscillator "
                        + "polynomial p. Finite charge expansion and induction on words put the original "
                        + "negative-word span inside this enlarged palette span.")),
                    Paragraph(Text("For q>M, let lambda_q extract the oscillator-constant coefficient in charge q. "
                        + "On actual charge/oscillator basis vectors, charge homogeneity and actual_mode_grade "
                        + "force a nonzero outer-insertion coefficient at a negative mode m to satisfy "
                        + "0=r+t+2ds(q-s)-m-1. If 0<s<=M, positivity of d and q-s makes this impossible. "
                        + "For s=0 a nonconstant oscillator monomial has strictly positive oscillator energy, "
                        + "giving the same vanishing. The remaining scalar oscillator constant is a multiple "
                        + "of the actual vacuum, whose field has identity mode -1 and zero at all other modes. "
                        + "Basis extension gives these insertion statements on arbitrary inputs. There is "
                        + "no positive-definite Gram or lower-bounded-total-energy premise.")),
                    Paragraph(Text("Strong induction on total word length proves that lambda_q kills every palette "
                        + "word. A word with only negative-charge labels has nonpositive total charge; this "
                        + "also handles the empty word. Otherwise take its first nonnegative-charge label a. "
                        + "An inner induction moves a left across its initial negative-charge prefix. "
                        + "Swapping adjacent labels b,a uses the actual finite mode_commutator. The j-th "
                        + "correction is the actual state b_j a at mode m+n-j. Charge homogeneity writes "
                        + "it as one palette label: its charge is charge(b)+charge(a), still in [-M,M], "
                        + "and its mode is strictly negative. Each correction replaces two factors by one. "
                        + "The outer induction therefore kills it with its full outer prefix and tail. "
                        + "The swapped term advances the inner induction. At the far left a positive "
                        + "label vanishes by the insertion calculation; a zero-charge label gives a scalar "
                        + "multiple of a shorter word under lambda_q. No same-sign commutation or assumed "
                        + "normal form is used.")),
                    Paragraph(Text("Consequently the enlarged palette span lies in ker(lambda_q), whereas "
                        + "lambda_q(single(charge(d,q),1))=1. Taking q=M+1 makes the enlarged span, "
                        + "and hence the original arbitrary-state span, proper."))),
                DescribeRole.Theorem),
            Paragraph(Text("The charge-palette and shorter-word proof is an author-supplied derivation from the "
                + "repository's actual_mode_grade, charge_homogeneity and finite mode_commutator. "
                + "The original lattice-field construction retains the Bakalov--Kac math/0402315v1 "
                + "section 4.1 attribution; its residue and locality suppliers retain their "
                + "Matsuo--Nagatomo and Carnahan attributions. Mathlib supplies basis extension, "
                + "finite-support expansion and linear spans. No external-literature novelty or "
                + "equivalence with other bracketing conventions is asserted.")))));
}

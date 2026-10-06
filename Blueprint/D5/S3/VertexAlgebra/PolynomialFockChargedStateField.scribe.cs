using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class PolynomialFockChargedStateFieldDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/PolynomialFockChargedStateField.";
    private static readonly LibraryNoteRef FreeBoson =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997freeboson");
    private static readonly LibraryNoteRef Locality =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/matsuo1997locality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every charged polynomial Fock field coefficient is a finite sum over positional deletions.",
        H("Charged Polynomial Fock Field Coefficients"),
        Blocks(
            Paragraph(Text("Let F=C[X_0,X_1,...] be the complex polynomial Fock space. "
                + "The actual current J has mode -j-1 equal to multiplication by X_j, "
                + "mode zero equal to zero, and mode j+1 equal to (j+1) times "
                + "partial differentiation in X_j, for every natural j. "
                + "Normalized mode n means Laurent power -n-1. The divided "
                + "derivative D_j is 1/j! times the ordinary formal derivative.")),
            Describe.Lean(
                DescribeId.Create("charged-polynomial-fock-current"),
                DeclarationHandle.Create(Prefix + "chargedCurrent"),
                H("The current of arbitrary complex charge"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(FreeBoson),
                Blocks(Paragraph(Text("For every complex lambda, chargedCurrent(lambda) "
                    + "is J plus the singleton Laurent field lambda z^(-1) id_F. "
                    + "Its normalized mode zero is lambda id_F, and every other "
                    + "normalized mode is the corresponding actual current mode. "
                    + "The sum is a field using J's lower truncation and the "
                    + "singleton's support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-polynomial-fock-word-field"),
                DeclarationHandle.Create(Prefix + "chargedWordField"),
                H("Right-nested ordered word fields"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Locality),
                Blocks(Paragraph(Text("For every complex lambda and finite natural "
                    + "word w, set W_lambda([])=identityField and "
                    + "W_lambda(j::w)=N(D_j chargedCurrent(lambda),W_lambda(w)), "
                    + "where N(A,B) is the existing ordered minus-one normal "
                    + "product. At integer mode n on input v its two branches are "
                    + "the pointwise finite sums over natural k of A_(-k-1) "
                    + "B_(n+k) v and B_(n-k-1) A_k v. This specifies the "
                    + "right nesting and the divided-derivative normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charged-polynomial-fock-state-field"),
                DeclarationHandle.Create(Prefix + "chargedY"),
                H("The monomial basis extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(FreeBoson),
                Blocks(Paragraph(Text("For every complex lambda, chargedY(lambda) "
                    + "is the complex linear map obtained from the existing "
                    + "basisMonomials(N,C) by assigning exponent e the field "
                    + "W_lambda(occurrences(e)). The existing occurrences(e) "
                    + "is the sorted list e.toMultiset.sort. Thus every "
                    + "polynomial is extended by its actual monomial coefficients."))),
                DescribeRole.Definition),
            Paragraph(Text("For a finite natural word w, let P(w)=Fin(length(w)). "
                + "For each subset R of P(w), keep(w,R) is List.finRange(length(w)) "
                + "filtered to positions outside R and then mapped by w.get. "
                + "Set s(w,R)=sum over i in R of (w.get(i)+1), as an integer, "
                + "and c(lambda,w,R)=product over i in R of ((-1)^(w.get(i)) lambda), "
                + "as a complex number. The empty sum is zero and the empty "
                + "product is one, for every lambda. Masks distinguish repeated "
                + "labels, and keep preserves both repetitions and relative order.")),
            Describe.Lean(
                DescribeId.Create("charged-polynomial-fock-state-field-coefficients"),
                DeclarationHandle.Create(Prefix + "charged_statefield_coefficients"),
                H("Every input polynomial and every integer mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(FreeBoson),
                Blocks(
                    Paragraph(Text("For every complex lambda, all u,v in F and every "
                        + "integer n, chargedY(lambda)(u)_n v equals the sum over "
                        + "e in the finite support of u and over every R in the "
                        + "powerset of the universal finite set P(occurrences(e)) "
                        + "of (coeff(e,u) c(lambda,occurrences(e),R)) acting by "
                        + "complex scalar multiplication on "
                        + "wordField(keep(occurrences(e),R))_(n-s(occurrences(e),R)) v. "
                        + "Here wordField is the existing zero-charge ordered word "
                        + "field, acting on the same arbitrary input v. There are "
                        + "no further hypotheses on the charge, polynomials or mode.")),
                    Paragraph(Text("The divided derivative of the singleton has "
                        + "only normalized mode j, with value (-1)^j lambda id_F. "
                        + "No factorial remains. It gives no correction in the "
                        + "negative branch, and its positive branch selects k=j "
                        + "and contributes (-1)^j lambda times the tail mode "
                        + "n-j-1. Word induction applies at every integer mode "
                        + "and to every input, including the actual derivative "
                        + "modes of the charged current applied to that input.")),
                    Paragraph(Text("Before sums are rearranged, each original "
                        + "branch and every separate transformed mask summand "
                        + "has finite support. Increasing right modes vanish "
                        + "on the fixed input in the forward branch. Increasing "
                        + "left modes vanish on that input in the reverse branch. "
                        + "For a transformed mask the forward bound uses the "
                        + "Laurent order of its retained word at the shifted mode; "
                        + "the reverse bound uses the left field on the original "
                        + "input. Their finite union justifies the exchanges. "
                        + "Every parent mask is uniquely a successor image of a "
                        + "tail mask or that image with position zero inserted. "
                        + "These alternatives preserve or remove the first label "
                        + "and give exactly the displayed weights and shifts.")),
                    Paragraph(Text("An empty word has only the empty mask. Its "
                        + "field is the identity, whose mode -1 is id_F and whose "
                        + "other integer modes are zero. A zero polynomial has "
                        + "empty support. Empty masks, full masks, zero charge, "
                        + "repeated labels and all mode signs are included in "
                        + "the same equality.")),
                    Paragraph(Text("Matsuo-Nagatomo's free-boson Sections 2.2-2.3 "
                        + "supply the polynomial mode conventions, and their "
                        + "locality Sections 1.2-1.4 supply the normalized "
                        + "coefficients, divided derivatives and residue conventions. "
                        + "These references provide background for the specified "
                        + "finite coefficient expansion; no mathematical novelty "
                        + "is asserted. Charged-module Jacobi, fusion, a Monster "
                        + "realization, complete string theory and AdS/CFT "
                        + "spacetime dynamics remain beyond this coefficient equality."))),
                DescribeRole.Theorem))));
}

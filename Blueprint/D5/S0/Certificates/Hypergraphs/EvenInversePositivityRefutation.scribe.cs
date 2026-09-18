using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Hypergraphs;

internal sealed class EvenInversePositivityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/Hypergraphs/EvenInversePositivityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/chaithrarani2025marked");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six four-element edges on eight vertices give inverse coefficient minus fourteen.",
        H("Even Hyperedges Do Not Ensure Inverse Positivity"),
        Blocks(
            Describe.Lean(DescribeId.Create("even-inverse-positivity-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The source equivalence for simple hypergraphs"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Section 8.1, PDF p. 23, states: “Let 𝒢 be a simple hypergraph. "
                        + "Then we have I(𝒢,−x)⁻¹ ≥ 0 if and only if all edges of 𝒢 "
                        + "must have even number of elements.” Mathematical glyphs and "
                        + "whitespace in the quotations are normalized; the prose is verbatim.")),
                    Paragraph(Text(
                        "Section 3.1, PDF p. 7, begins: “Let n be a positive integer.” "
                        + "Definition 2(1), p. 7, says: “A hypergraph 𝒢 is called simple "
                        + "if for any e,f ∈ ℰ, we have |e| ≥ 2 and e ⊆ f implies e = f.” "
                        + "Definition 2(5), p. 7, says: “A subset I ⊆ 𝒱 is called independent "
                        + "if no edge of 𝒢 is entirely contained in I, i.e., e ⊈ I for all e ∈ ℰ.”")),
                    Paragraph(Text(
                        "The formula expands SourceSimple into its edge-size and inclusion "
                        + "conditions. Fin n relabels the source vertex set [n]. Finsupp(Fin n,Nat) "
                        + "is the type Fin n →₀ Nat of all exponent multiindices. The signed "
                        + "independence series belongs to MvPowerSeries (Fin n) ℚ: for every "
                        + "independent subset S it has the monomial with exponent indicator S "
                        + "and coefficient (−1)^|S|, where indicator S is one on S and zero elsewhere. "
                        + "Definition 3, p. 7, sums over all independent subsets, including the "
                        + "empty subset. Consequently the constant coefficient is one. "
                        + "The coefficient ring is rational (p. 1), and the order is coefficientwise "
                        + "(p. 2); the assertion concerns every multiindex, not only squarefree ones. "
                        + "This is the ordinary independence polynomial, without a choice of marked vertices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-inverse-positivity-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An eight-vertex counterexample"),
                StatementSource.FromAuthor(F.Disp(new Formula.Not(Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Label vertices 0,…,7 by a1,a2,a3,b1,b2,b3,s,t. Take the edges "
                        + "{6,7,0,1}, {6,7,1,2}, {6,7,2,0}, {6,7,3,4}, {6,7,4,5}, "
                        + "and {6,7,5,3}. These are six distinct four-element sets. Thus every "
                        + "edge has even size at least two, and containment between edges forces equality.")),
                    Paragraph(Text(
                        "For a subset T, put i = |T ∩ {0,1,2}| and j = |T ∩ {3,4,5}|. "
                        + "Let d(0),d(1),d(2),d(3) be 1,1,0,−4, respectively. Set c(T)=1 "
                        + "when T does not contain both 6 and 7, and c(T)=2−d(i)d(j) otherwise. "
                        + "For a subset U let f(U)=(−1)^|U| when U is independent, and f(U)=0 "
                        + "otherwise. The exact subset convolution satisfies c(∅)=1 and, for "
                        + "nonempty T, c(T)=−∑_{∅≠U⊆T} f(U)c(T∖U).")),
                    Paragraph(Text(
                        "The actual formal inverse has constant coefficient one. A decomposition "
                        + "of the squarefree exponent indicator T is uniquely a subset U of T "
                        + "and its complement T∖U. Its coefficient recurrence is therefore precisely "
                        + "the displayed subset convolution. Induction on |T| identifies c(T) "
                        + "with the actual inverse coefficient; every nonempty U leaves a smaller "
                        + "complement. At the full vertex set the coefficient is 2−(−4)(−4)=−14. "
                        + "This single negative coefficient contradicts the even-edges-to-positivity "
                        + "direction and hence refutes the full equivalence.")),
                    Paragraph(Text(
                        "The same coefficient has a compact algebraic explanation. Write "
                        + "A=∏(1−a_i), B=∏(1−b_i), J_A=1−a1−a2−a3 and J_B=1−b1−b2−b3. "
                        + "The signed independence polynomial is F=(1−s−t)AB+stJ_AJ_B, "
                        + "so [st]F⁻¹=2/(AB)−J_AJ_B/(A²B²). The coefficient of a1a2a3 "
                        + "in J_A/A² is 8−3·4=−4, and the b coefficient is identical. "
                        + "The full squarefree coefficient is thus 2−16=−14. This expresses "
                        + "the same counterexample and certificate."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("even-hypergraph-inverse-positivity-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula ClaimFormula() => F.Disp(Equal(Id("claim"),
        All("n", Id("Nat"), Implies(Rel(Num(0), FormulaRelationOperator.LessThan, Id("n")),
            All("E", Call("Finset", EdgeType()), Implies(SimpleFormula(),
                new Formula.Logic(
                    All("m", Call("Finsupp", Call("Fin", Id("n")), Id("Nat")),
                        Rel(Num(0), FormulaRelationOperator.LessThanOrEqual,
                            Call("coeff", Id("m"),
                                new Formula.Power(Call("signedIndependence", Id("E")),
                                    new Formula.Negate(Num(1)))))),
                    FormulaLogicOperator.Iff,
                    All("e", EdgeType(), Implies(Member("e"),
                        Call("Even", Call("card", Id("e"))))))))))));

    private static Formula SimpleFormula() => new Formula.Logic(
        All("e", EdgeType(), Implies(Member("e"),
            Rel(Num(2), FormulaRelationOperator.LessThanOrEqual, Call("card", Id("e"))))),
        FormulaLogicOperator.And,
        All("e", EdgeType(), Implies(Member("e"),
            All("f", EdgeType(), Implies(Member("f"),
                Implies(Rel(Id("e"), FormulaRelationOperator.SubsetOf, Id("f")),
                    Equal(Id("e"), Id("f"))))))));

    private static Formula EdgeType() => Call("Finset", Call("Fin", Id("n")));
    private static Formula Member(string name) =>
        Rel(Id(name), FormulaRelationOperator.MemberOf, Id("E"));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class CappedUnionDavenportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/CappedUnionDavenport.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Semigroups/mazhang2026wangcounterexamples");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every relative Davenport constant of the capped union monoid P_fin(U) x {0,1,2} equals |A|+k.",
        H("Relative Davenport constants of the capped union monoid"),
        Blocks(
            Node("capped-element", "Elements of S_U", "Capped",
                Disp(Equal(Call("Capped", F.Id("U")), Call("Prod", Call("Finset", F.Id("U")), Call("Fin", D(3))))),
                "An element of S_U is a pair (A,i) of a finite subset A of U and a level i in {0,1,2}. With decidable equality on U, addition is (A,i)+(B,j)=(A union B, min(2,i+j)) and the identity is (empty,0); these make S_U a commutative monoid, and a finite sum has the union of the supports and the capped total level.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("capped-minimal", "Minimal sequences", "MinimalFor",
                Disp(Iff(Call("MinimalFor", F.Id("f"), F.Id("t")), And(Equal(Call("sum", F.Id("f")), F.Id("t")),
                    All("I", Call("Finset", Call("Fin", F.Id("n"))), Imp(NotEqual(F.Id("I"), F.Id("univ")),
                        NotEqual(Call("sum", F.Id("I"), F.Id("f")), F.Id("t"))))))),
                "In any commutative monoid M, a sequence f of length n sums to t and no proper subsequence, indexed by a proper subset of the positions and including the empty one, sums to t.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("capped-lengths", "Lengths of minimal sequences", "minimalLengths",
                Disp(Equal(Call("minimalLengths", F.Id("t")), Seq(Open, F.Id("n"), Colon, Sp, Ex("f", Arrow(Call("Fin", F.Id("n")), F.Id("M")), Call("MinimalFor", F.Id("f"), F.Id("t"))), Close))),
                "For a commutative monoid M and t in M, the relative Davenport constant D_t(M) is the supremum of this set of lengths.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("capped-result", "D_(A,k)(S_U)=|A|+k", "result",
                Disp(All("A", Call("Finset", F.Id("U")), All("k", Call("Fin", D(3)),
                    Call("IsGreatest", Call("minimalLengths", Call("pair", F.Id("A"), F.Id("k"))), Add(Call("card", F.Id("A")), F.Id("k")))))),
                "For every type U, finite A and k in {0,1,2}, the set of lengths of minimal sequences with sum (A,k) has greatest element |A|+k; in particular D_(empty,0)=0. Lower bound: the singletons ({a},0) for a in A followed by k copies of (empty,1) sum to (A,k), and a proper subfamily either omits a singleton, losing its point, or omits a copy of (empty,1), dropping the capped level below k. Upper bound: in a minimal sequence each single deletion changes the sum. A term whose deletion keeps the capped level must be the only term containing some point of A, and distinct such terms give distinct points, so there are at most |A| of them. A term whose deletion lowers the capped level has level at least 1 and at least L-1 for the total level L, and at most min(2,L)=k terms can satisfy this. This is Lemma 4 of Ma and Zhang, Zenodo 10.5281/zenodo.23884901.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)))));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
}

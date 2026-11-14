using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PermutationCriteria;

internal sealed class ClarisseWocjanClassificationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/clarissewocjan2005permutationcriteria");

    public DocumentDefinition Create()
    {
        Formula r = F.Id("r"), d = F.Id("d"), sigma = F.Id("sigma"), mu = F.Id("mu");
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula permutations = Call("Perm", Call("Fin", Mul(Num(2), r)));
        Formula s = Call("rowSet", sigma), t = Call("rowSet", mu);
        Formula js = Call("map", Call("J", r), s);
        Formula statement = All([Bound("r", natural), Bound("d", natural)],
            Implies(And(Le(Num(1), r), Le(Num(2), d)),
                All([Bound("sigma", permutations), Bound("mu", permutations)],
                    Iff(Call("Dependent", r, d, sigma, mu),
                        Or(Eqn(t, s), Or(Eqn(t, Call("complement", s)),
                            Or(Eqn(t, js), Eqn(t, Call("complement", js)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Permutation criteria have equal trace norms on every density matrix exactly when their row-position sets differ by the four universal symmetries.",
            H("Complete classification of permutation norm dependence"), Blocks([
                .. InvarianceDescriptions.Items(),
                Describe.Lean(DescribeId.Create("clarisse-wocjan-permutation-classification-result"),
                    DeclarationHandle.Create("D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification.result"),
                    H("The four row-set symmetries are complete"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(Source),
                    Blocks(Paragraph(Text(
                        "For every natural number r at least one, every natural local dimension d at least two, and every two permutations sigma and mu of Fin (2r), norm dependence holds if and only if rowSet(mu) equals rowSet(sigma), its complement, its image under J r, or the complement of that image. "
                        + "A matrix is indexed by functions Fin r to Fin d. It is a density matrix exactly when it is positive semidefinite and has trace one. Position 2k is ket and 2k+1 is bra; permute sigma rho at a,b is rho at the even and odd projections of p mapped to merge a b (sigma p). rowSet(sigma) is the preimage of the even output positions. J r exchanges 2k and 2k+1 for every k. Complements are taken in Fin (2r). "
                        + "Dependent quantifies over every such density matrix and asserts equality of the two real trace norms. The trace norm is real trace of sqrt(A adjoint times A); adjoint invariance also gives the source convention sqrt(A times A adjoint). "
                        + "Equal row sets give independent row and column permutations. Complementation gives transpose. Simultaneous ket-bra exchange gives entrywise conjugation on Hermitian inputs. A maximally mixed local qubit distinguishes equal-side from opposite-side positions. A Bell pair distinguishes the three pair distances between paired side labels, with norms 1, sqrt(2), and 2. Independent flips in the same-side and opposite-side sectors recover the row set up to the four symmetries. "
                        + "This settles equality of norm functions in Definition 1. It does not assert incomparability of the sets of states detected by the criteria, the stronger notion called truly independent in the source. The closed count of dependence classes requires an additional orbit-count argument."))),
                    DescribeRole.Theorem, new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("clarisse-wocjan-2005-permutation-criteria-classification"),
                        ResolutionKind.Proved))]), []));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eqn(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Implies(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Or, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
}

internal static class InvarianceDescriptions
{
    private const string Module = "D5/S3/Quantum/Entanglement/PermutationCriteria/ClarisseWocjanClassification";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Eigenstructure/clarissewocjan2005permutationcriteria");

    public static DocumentBlock[] Items() => [

            Describe.Lean(
                DescribeId.Create("permutation-norm-equal-row-subsets"),
                DeclarationHandle.Create(Module + ".traceNorm_eq_of_rowSet"),
                H("Equal row subsets give equal trace norms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all natural r and d, all permutations sigma and mu of "
                    + "the 2r interleaved positions, and every complex operator rho on the r-fold d-dimensional "
                    + "tensor index set, equality of rowSet(mu) and rowSet(sigma) implies "
                    + "traceNorm(permute(mu,rho))=traceNorm(permute(sigma,rho)). A row subset consists of "
                    + "the original positions which the permutation sends to even output positions. "
                    + "The permutation mu composed with the inverse of sigma preserves parity. Its restrictions "
                    + "to the even and odd positions induce independent bijections of the row and column "
                    + "tensor coordinates. The two permuted matrices therefore differ by independent reindexing. "
                    + "No positivity or trace assumption is required for this equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("permutation-norm-four-symmetries"),
                DeclarationHandle.Create(Module + ".dependent_of_rowSet_orbit"),
                H("The four row-subset symmetries preserve dependence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For all natural r and d and all permutations sigma and mu, "
                    + "the criteria are dependent whenever rowSet(mu) equals rowSet(sigma), its complement, "
                    + "its image under the simultaneous exchange J of each factor's ket and bra positions, "
                    + "or the complement of that image. Dependence means equality of the two permuted trace "
                    + "norms on every positive semidefinite operator of trace one. Complementing the output "
                    + "row positions transposes the permuted matrix. Applying J to the original positions "
                    + "complex-conjugates every entry because a density matrix is Hermitian. Transpose and "
                    + "entrywise conjugation preserve the trace norm. The equal-row-subset theorem then covers "
                     + "every permutation representing any of these four subsets. This sufficient direction "
                    + "concerns equality of norm functions. It does not establish incomparability of "
                    + "detection sets for criteria in different orbits."))),
                DescribeRole.Theorem)
    ];
}

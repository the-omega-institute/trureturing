using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class DasMohantySingularSquaredDistanceDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/SpectralGraph/DasMohantySingularSquaredDistance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal singular multipartite source Laplacian has a verified rank-one reduction; "
        + "the complete positive multiplicity and inertia conjecture remains open.",
        H("Singular multipartite squared-distance Laplacian"), Blocks(
            Paragraph(Text(
                "The source is Joyentanuj Das and Sumit Mohanty, Inverse of the Squared Distance "
                + "Matrix of a Complete Multipartite Graph, arXiv:2311.01069v2, equation (3.6) "
                + "and the concluding conjecture; DOI 10.13001/ela.2024.8283. The author-defined "
                + "omitted-list equalities determine the hats. The inconsistent expanded hatted "
                + "Psi products are not substituted for those definitions. No publisher correction, "
                + "priority or worldwide literature-completeness claim is made.")),
            Paragraph(Text(
                "For any natural t and n:Fin(t) to Nat, the vertex carrier is the dependent sum "
                + "of Fin(n(i)). Set d(i)=3n(i)-4. For a finite parameter set S, phi(n,S) is the "
                + "product of d(i) over S, psi(n,S) is the sum of n(i)phi(n,S without i), "
                + "and theta=phi+psi. Empty products are one and empty sums zero. Restricting S "
                + "therefore removes exactly the indicated parameters, including for double hats. "
                + "ratio(n) is the sum of n(i)/d(i).")),
            Paragraph(Text(
                "delta(n) has diagonal zero, within-part off-diagonal four and between-part one. "
                + "For t at least two and positive part sizes these are the squared graph distances. "
                + "cofactorSum is the sum of every adjugate entry, hence the sum of all cofactors, "
                + "not a principal cofactor. sourceL uses the literal three source cases: its "
                + "diagonal numerator is (n(i)-1)theta(hat i)/2+(n(i)-3)psi(hat i), divided by "
                + "2psi; its within-part off-diagonal entry is -(theta(hat i)/2+psi(hat i))/(2psi); "
                + "its between-part entry is phi(hat i,hat j)/psi.")),
            Paragraph(Text(
                "blockBase=3 times the partwise all-ones matrix minus 4I. Its explicit inverse "
                + "has same-part coefficient 3/(4d(i)) and diagonal subtraction 1/4. A is the "
                + "negative of this inverse and z has vertex value 1/d(i). All these are actual "
                + "matrices on the original vertex carrier. No matrix identity, realization, "
                + "classification or spectral-transfer premise is introduced.")),
            Entry("singular_source_downdate", "Literal source rank-one identity", Context(
                And(Ne(Call("psi", N, C("univ")), D(0)), And(
                    Eqn(Call("pivot", Call("A", N), C("oneVector")), D(1)),
                    Eqn(Call("sourceL", N),
                        Call("downdate", Call("A", N), C("oneVector")))))),
                "Positive integer sizes imply each d(i) is nonzero. The explicit block inverse "
                + "is checked by multiplication. Multiplying delta by it gives I+z times the "
                + "all-ones row. The existing determinant lemma then makes singularity imply "
                + "ratio=-1 and psi=-phi, so every source denominator is nonzero. Separating "
                + "omitted summands and substituting into all three source entry cases proves "
                + "sourceL=A-zz-transpose. The quadratic pivot of A on the ones vector is one. "
                + "This is a source-specific application of the existing determinant machinery."),
            Entry("singular_source_reduction", "Inertia transfer and positive eigenvector families",
                null,
                "The quantified conclusion supplies a Hermitian sourceL. Its positive index plus "
                + "one is the positive index of A, its negative index equals that of A, and its "
                + "zero eigenvalue multiplicity is exactly one. Every vector whose sum in each "
                + "part is zero is an eigenvector with value 1/4. Every vector supported on "
                + "singleton parts whose total sum is zero is an eigenvector with value one. "
                + "The existing structured rank-one inertia theorem is applied with the actual "
                + "A, the ones vector and the derived pivot one. Invertibility of A excludes "
                + "zero eigenvalues before the downdate. The action identities are proved on "
                + "the actual source entries. The actual partwise-zero-sum subspace has dimension "
                + "N-t, by a surjective part-sum map and rank-nullity. These statements do not "
                + "assume the desired spectral counts."),
            Describe.Lean(DescribeId.Create("das-mohanty-complete-target"),
                DeclarationHandle.Create(Owner + "completeConjecture"),
                H("The complete target"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "completeConjecture retains every t at least two, all positive integer sizes, "
                    + "nonzero sum of all cofactors and singular delta. Let N be the sum of sizes, "
                    + "s the number of sizes at least two and h the number equal to one. Its "
                    + "conclusion is the conjunction of: the positive real characteristic-root "
                    + "multiset equals N-t copies of 1/4 plus h-1 copies of one; and the "
                    + "positive, zero, negative indices equal N-s-1, one, s. Multisets preserve "
                    + "algebraic multiplicity, and Hermitian symmetry connects them to the "
                    + "indexed eigenvalues. This definition is a target, not a proof. The "
                    + "remaining formal obligations are the exact sign counts of A, dimensions "
                    + "of the singleton-supported source eigenspace, and exhaustion of the positive spectrum. "
                    + "The boundary cases remain in the quantified domain. No partial result "
                    + "settles either complete source clause."))), DescribeRole.Definition))));

    private static DocumentBlock Entry(string name, string title, Formula? formula, string prose) =>
        Describe.Lean(DescribeId.Create("das-mohanty-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Owner + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula N => F.Id("n");
    private static Formula C(string s) => Seq(Operatorname, Grp(F.Id(s)));
    private static Formula Call(string s, params Formula[] args) =>
        new Formula.Apply(C(s), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Context(Formula body) => All("t", C("Nat"),
        All("n", Seq(Call("Fin", F.Id("t")), Sp, To, Sp, C("Nat")),
            Imp(Call("PositiveParts", N), Imp(Eqn(Call("det", Call("delta", N)), D(0)), body))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class SymbolicHyperplaneGeneralPositionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/SymbolicHyperplaneGeneralPosition.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/razwigderson2019subspace");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One symbolic hyperplane for a constant arrangement",
        H("One symbolic hyperplane for a constant arrangement"),
        Blocks(
            Paragraph(Text("Let F be a characteristic-zero field, A a finite coordinate type, I any index type, and K=Frac(F[T(a): a in A]). The polynomial variables T(a) are independently indeterminate; they are mapped into their fraction field. Coord(A,F) denotes F^A. For v in F^A let c(v)(a) be the scalar inclusion of v(a) in K, and let Ext(V)=span_K c(V), with ExtFamily(V)(i)=Ext(V(i)). The symbol bottom denotes the zero subspace. The one prescribed functional N(F,A) sends w to the sum over a of T(a)w(a). GP is exactly InGeneralPosition from ActualWindowCommonKernel: every indexed member is not contained in ker(N(F,A)), and for all finite subfamilies A0,B0,C0 contained in s, (Tcut(A0)+S(B0)) intersect (Tcut(A0)+S(C0)) being contained in ker(N(F,A)) implies that this intersection equals Tcut(A0). Here S is the span of the uncut members and Tcut is the span of their individual cuts. Empty subfamilies, overlaps and equal subspaces at different indices are permitted.")),
            Describe.Lean(DescribeId.Create("symbolic-normal-exact-general-position"),
                DeclarationHandle.Create(Prefix + "symbolic_general_position"),
                H("The independent normal satisfies both general-position clauses"),
                StatementSource.FromAuthor(Disp(GeneralPosition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Pinned Mathlib supplies polynomial derivations with prescribed values on the variables and the base-change isomorphism for the module of differentials under localization. Together they give, for every rational direction y, an F-derivation d_y of K with d_y(T(a))=y(a). It acts coordinatewise on vectors and obeys the product rule. Constant vectors have derivative zero, so every extended uncut subspace is stable under differentiation. Differentiating N(c(v))=0 in each coordinate direction shows v=0, which gives memberwise nonvanishing.")),
                    Paragraph(Text("For the intersection clause put T=Tcut(A0) and J=(T+S(B0)) intersect (T+S(C0)), and assume J is contained in ker(N). Let psi be any K-linear functional annihilating T. Choose y(a)=psi(e(a)). The product rule gives d_y(N(v))=N(d_y(v))+psi(v). For v in a constituent cut of T, psi(v)=0 and N(v)=0; therefore N(d_y(v))=0. Its uncut subspace is stable as well, so every constituent cut, T, both sums and J are stable. For w in J, both N(w) and N(d_y(w)) vanish, hence psi(w)=0. The double-annihilator theorem gives w in T. The reverse inclusion is a lattice inclusion. This proves the full intersection clause, without a disjointness or nonemptiness restriction on A0,B0,C0.")),
                    Paragraph(Text("This is the symbolic genericity input used in R5 (31.6)-(31.7), corresponding to Raz and Wigderson, Theorem 7.1 and its fraction-field Claim 7.2. The displayed conclusion is literature-attested; the directional-derivation proof is a repository derivation. No novelty or finite-field probability bound is claimed. Allowing the subspaces to depend on T would invalidate the constant-subspace stability step."))), DescribeRole.Theorem),
            Paragraph(Text("For the application let B be a finite block type, J(i) a finite coordinate type for each block, and C the dependent sum of the J(i). Set K=Frac(F[T(c): c in C]). A base array b(i,sigma,j) is F-valued, and Lift(b)(i,sigma,j) is its scalar inclusion into K. BlockRows places the indicated row in its own block and zero elsewhere. Normal(T) is the coefficientNormal functional with the prescribed independent tuple T in every row. CR(b,k,s) is the K-dimension of commonRowSpan(BlockRows(Lift(b)),Normal(T),k,s), always with this prescribed normal. The distinguished base row b(k,sigma) is required to be nonzero for every sigma in s. Cost(b,P) is the sum over blocks A0 of P of [(sum over i of dim_K blockSpan(Lift(b),A0,i))-1], with natural-number subtraction inside each summand. Finpartition(s) partitions s into nonempty disjoint blocks and admits the empty partition when s is empty.")),
            Describe.Lean(DescribeId.Create("symbolic-common-block-partition-rank"),
                DeclarationHandle.Create(Prefix + "symbolic_block_common_rows_partition_rank"),
                H("The common-row partition formula with genericity discharged"),
                StatementSource.FromAuthor(Disp(BlockRank())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Flatten the dependent coordinate blocks and take V(sigma) to be the F-span of their block-supported base rows. The nonzero distinguished row makes V(sigma) nonzero. Scalar extension commutes with these spans. The preceding general-position theorem applies to this constant arrangement, and the linear equivalence between flat and block coordinates transports its complete predicate. The distinguished symbolic coefficient is nonzero by the same coordinate-derivation argument. Feeding these two proved facts into ActualWindowCommonKernel.block_common_rows_partition_rank gives an attaining partition and every-partition upper bound. This is a live use of exact symbolic general position in the common-constraint application, with no GP antecedent in the displayed statement.")),
                    Paragraph(Text("For the actual embedding application of R5, take F here to be the normal-closure field K_0 of the excerpt and b(i,sigma,j)=sigma(x(i,j)), before adjoining the common parameter tuple. This substitution produces the actual rows of (31.6) and the partition formula in terms of their scalar-extended block-span dimensions. The theorem does not identify those dimensions with degrees of intermediate fields, prove distinctness or completeness of the embedding family, establish independence of the h-1 original common rows, identify the rank of the original-F polynomial map, prove Galois descent or uniqueness of a fewest-block optimum, or return an original-F simultaneous attaining tuple. Those remain separate obligations of the source. The following theorem supplies the missing row-basis assertion. Four-slot Reg registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29247; no declared_validated status is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("symbolic-common-block-basis-partition-rank"),
                DeclarationHandle.Create(Prefix + "symbolic_block_common_rows_basis_partition_rank"),
                H("The displayed common rows form the exact cut basis and attain partition rank"),
                StatementSource.FromAuthor(Disp(BasisRank())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Assume every base row b(i,sigma) is nonzero on the finite family. The same independent coordinate tuple is used in every block and every embedding. For each sigma, the rows indexed by i different from the distinguished k are linearly independent: inspecting block i isolates its coefficient, while the common coefficient U(k,sigma) and the selected coordinate of b(i,sigma) are both nonzero. The distinguished row is zero, so these h-1 rows span exactly the scalar-extended block-row space intersected with the one common kernel hyperplane.")),
                    Paragraph(Text("The theorem combines that explicit basis statement with the preceding symbolic partition-rank result. It returns one attaining nonempty-block partition and the upper bound for every partition, with no general-position premise, no quotient construction and no Galois descent. The coefficient tuple is the same coordinate family used by coefficientNormal throughout (31.6). For normalized embedding bases whose first entry is one, the row nonvanishing premise is immediate. This closes the source's basis clause but leaves the later intermediate-field identifications and original-field specialization outside this declaration. Four-slot Reg registration remains unfinished under https://github.com/the-omega-institute/trureturing/issues/29247; no declared_validated status is asserted."))), DescribeRole.Theorem))));

    private static Formula GeneralPosition()
    {
        Formula result = App(I("GP"), App(I("ExtFamily"), I("V")), App(I("N"), I("F"), I("A")), I("s"));
        Formula nonzero = All("i", I("I"), Imp(
            Rel(I("i"), FormulaRelationOperator.MemberOf, I("s")),
            Rel(App(I("V"), I("i")), FormulaRelationOperator.NotEqual, I("bottom"))));
        result = All("V", Arrow(I("I"), App(I("Submodule"), I("F"), App(I("Coord"), I("A"), I("F")))),
            All("s", App(I("Finset"), I("I")), Imp(nonzero, result)));
        result = Inst(App(I("CharZero"), I("F")), result);
        result = Inst(App(I("Fintype"), I("A")), result);
        result = Inst(App(I("Field"), I("F")), result);
        return All("F", Ty(), All("A", Ty(), All("I", Ty(), result)));
    }

    private static Formula BlockRank()
    {
        Formula rank = App(I("CR"), I("b"), I("k"), I("s"));
        Formula result = Ex("P", App(I("Finpartition"), I("s")),
            And(Eq(rank, App(I("Cost"), I("b"), I("P"))),
                All("Q", App(I("Finpartition"), I("s")),
                    Rel(rank, FormulaRelationOperator.LessThanOrEqual,
                        App(I("Cost"), I("b"), I("Q"))))));
        Formula nonzero = All("sigma", I("I"), Imp(
            Rel(I("sigma"), FormulaRelationOperator.MemberOf, I("s")),
            Rel(App(I("b"), I("k"), I("sigma")), FormulaRelationOperator.NotEqual, D(0))));
        result = All("b", All("i", I("B"), Arrow(I("I"), Arrow(App(I("J"), I("i")), I("F")))),
            All("k", I("B"), All("s", App(I("Finset"), I("I")), Imp(nonzero, result))));
        result = Inst(All("i", I("B"), App(I("Fintype"), App(I("J"), I("i")))), result);
        result = Inst(App(I("Fintype"), I("B")), result);
        result = Inst(App(I("CharZero"), I("F")), result);
        result = Inst(App(I("Field"), I("F")), result);
        return All("F", Ty(), All("I", Ty(), All("B", Ty(),
            All("J", Arrow(I("B"), Ty()), result))));
    }

    private static Formula BasisRank()
    {
        Formula row = App(I("commonRow"), I("b"), I("k"), I("sigma"), I("i"));
        Formula basis = And(App(I("LinearIndependent"), row),
            Eq(App(I("span"), row), App(I("cut"), I("b"), I("k"), I("sigma"))));
        Formula rank = App(I("CR"), I("b"), I("k"), I("s"));
        Formula result = Ex("P", App(I("Finpartition"), I("s")),
            And(All("sigma", I("I"), Imp(
                    Rel(I("sigma"), FormulaRelationOperator.MemberOf, I("s")), basis)),
                And(Eq(rank, App(I("Cost"), I("b"), I("P"))),
                    All("Q", App(I("Finpartition"), I("s")),
                        Rel(rank, FormulaRelationOperator.LessThanOrEqual,
                            App(I("Cost"), I("b"), I("Q")))))));
        Formula nonzero = All("sigma", I("I"), Imp(
            Rel(I("sigma"), FormulaRelationOperator.MemberOf, I("s")),
            All("i", I("B"), Rel(App(I("b"), I("i"), I("sigma")),
                FormulaRelationOperator.NotEqual, D(0)))));
        result = All("b", All("i", I("B"), Arrow(I("I"), Arrow(App(I("J"), I("i")), I("F")))),
            All("k", I("B"), All("s", App(I("Finset"), I("I")), Imp(nonzero, result))));
        result = Inst(All("i", I("B"), App(I("Fintype"), App(I("J"), I("i")))), result);
        result = Inst(App(I("Fintype"), I("B")), result);
        result = Inst(App(I("CharZero"), I("F")), result);
        result = Inst(App(I("Field"), I("F")), result);
        return All("F", Ty(), All("I", Ty(), All("B", Ty(),
            All("J", Arrow(I("B"), Ty()), result))));
    }

    private static Formula I(string name) => F.Id(name);
    private static Formula Ty() => Seq(I("Type"), Star);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Eq(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, p);
    private static Formula Ex(string n, Formula t, Formula p) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, p);
    private static Formula Inst(Formula t, Formula p) => Seq(OpenBracket, t, CloseBracket, Comma, Sp, p);
}

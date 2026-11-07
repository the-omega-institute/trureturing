using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Matroids;

internal sealed class FiniteIntersectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two matroids on a common finite ground have an attained intersection min-max equality.",
        H("Finite matroid intersection"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-matroid-intersection"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Matroids/FiniteIntersection.finite_matroid_intersection"),
            H("A common independent set and an attaining rank cut"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/FiniteGeometry/schrijver2017coursecombinatorialoptimization")),
            Blocks(
                Paragraph(Text(
                    "Let alpha be any type in an arbitrary universe u, E a finite subset of alpha, and M1 and M2 matroids whose grounds both equal E. There are sets I and X, both contained in E, such that the same I is independent in both matroids and its cardinality equals the rank of X in M1 plus the rank of E minus X in M2. For every set J independent in both matroids and every set Y in alpha, the cardinality of J is at most the rank of Y in M1 plus the rank of E minus Y in M2.")),
                Paragraph(Text(
                    "Cardinality is Set.ncard and rank is ENat.toNat of the native Matroid.eRk. Finiteness of the common ground makes every rank finite, even when alpha is infinite. Empty grounds, loops and rank zero are included. No representation over a field or positivity assumption is required. Although the attaining X lies in E, the upper bound permits every Y; it therefore also holds for every Y contained in E.")),
                Paragraph(Text(
                    "Theorem 10.9 on page 188 of Schrijver's course states the maximum cardinality of a common independent set as the minimum of the two-rank cut sum. The finite-ground definition is on page 173. The existential equality and the universal bound exhibit both attained extrema: use the attaining cut to bound every common independent set, and use the attaining independent set to bound every cut sum from below.")),
                Paragraph(Text(
                    "The proof proceeds by induction on the ground cardinality. If every element is a loop in at least one matroid, the empty independent set and the loop set of the first matroid give equality. Otherwise a common nonloop gives smaller deletion and contraction pairs. Their two common-independent certificates combine with submodularity in each matroid; failure of attainment would force the combined cut ranks to exceed the submodular upper bound. Splitting a common independent set at an arbitrary cut gives the universal inequality.")),
                Paragraph(Text(
                    "An application is the independent-cover criterion. Let alpha be any type, let M : Matroid alpha have finite ground M.E, and let k be any natural number, including zero. There exists one family I : Fin k -> Set alpha such that M.Indep (I i) holds for every i and the indexed union of I equals M.E if and only if, for every U : Set alpha contained in M.E, U.ncard is at most k times (M.eRk U).toNat. The existential quantifier supplies a single family covering the whole ground. Its k labeled slots may be empty, repeated or overlapping; no disjointness hypothesis is imposed.")),
                Paragraph(Text(
                    "Here Set.ncard is the ordinary cardinality of a finite set, and ENat.toNat converts a finite extended rank to its natural-number value. Every U under consideration is finite because it lies in M.E, and every rank used below is finite. Thus neither the cardinality nor the rank conversion loses information. Only the ground is assumed finite: alpha itself may be infinite, and no field representation is involved.")),
                Paragraph(Text(
                    "For the sufficient direction, assume the subset inequalities. Put beta equal to the ground subtype {e : alpha // e belongs to M.E} and N equal to M.restrictSubtype M.E. This gives a finite type beta and a matroid N whose ground is all of beta. On the finite type Fin k x beta, take S = Matroid.sum' (fun _ : Fin k => N) and Q = (Matroid.freeOn (Set.univ : Set beta)).comap Prod.snd. Both grounds are the full product, denoted Omega. The first constructor assigns one copy of N to each label; the second permits at most one chosen pair for each ground element.")),
                Paragraph(Text(
                    "For a subset A of the product, write A_i for the fiber {b : beta | (i,b) belongs to A}, and write r_N and r_S for the corresponding natural ranks. The native Matroid.sum'_indep_iff identifies S-independence with N-independence of every fiber. The rank of A in S is the sum, over i : Fin k, of r_N(A_i): choose a basis of A in S, apply Matroid.sum'_isBasis_iff to its fibers, and use Matroid.IsBasis.eRk_eq_encard. The images of these basis fibers under b -> (i,b) are disjoint and exhaust the basis; Set.encard_iUnion_of_finite and injective-image cardinality give the sum, and ENat.toNat_sum converts it because the ranks are finite. For Q, Matroid.comap_indep_iff makes Prod.snd injective on an independent set, while Matroid.eRk_comap and Matroid.eRk_freeOn identify the rank of A with the cardinality of its second-coordinate image.")),
                Paragraph(Text(
                    "Apply finite_matroid_intersection to S and Q on Omega. It supplies the same set J independent in both matroids and an attaining cut X contained in Omega, with the cardinality of J equal to r_S(X) plus the Q-rank of Omega minus X. Define T = Prod.snd '' (Omega minus X), and let U be the complement of T in beta. Every fiber X_i contains U: if (i,b) were outside X, then b would belong to T. The assumed inequality transfers to U through Subtype.val, since this map is injective, its image lies in M.E, and the restriction and comap rank identities give r_N(U) = (M.eRk (Subtype.val '' U)).toNat.")),
                Paragraph(Text(
                    "Consequently the cardinality of U is at most k times r_N(U). Rank monotonicity in each fiber bounds this product by the sum of r_N(X_i), which is r_S(X). The Q-rank of Omega minus X is the cardinality of T. Since U and T partition beta, their cardinalities sum to the cardinality of beta. Combining these facts with the equality for this same J and X shows that the cardinality of beta is at most the cardinality of J.")),
                Paragraph(Text(
                    "Q-independence makes Prod.snd injective on J, so the image Prod.snd '' J has exactly the cardinality of J. It is contained in beta, a finite set; the preceding lower bound and Set.eq_of_subset_of_ncard_le therefore force Prod.snd '' J to be all of beta. S-independence gives N-independence of every J_i. Define the original cover by I i = Subtype.val '' J_i for every label i. Matroid.restrictSubtype_indep_iff transfers each fiber's independence to M. Surjectivity of the second-coordinate image supplies a label for each element of M.E, and every image lies in M.E. Hence this one indexed union equals M.E.")),
                Paragraph(Text(
                    "Conversely, suppose one independent family I has indexed union M.E, and fix any target U contained in M.E. The sets U intersect I i have union U, even when the slots overlap. Set.ncard_iUnion_le_of_fintype bounds the cardinality of U by the sum of their cardinalities. Each intersection is independent in M; Matroid.Indep.eRk_eq_encard and Matroid.eRk_mono bound its cardinality by (M.eRk U).toNat. Summing over the k labels gives exactly the required upper bound by k times this rank. This direction uses a union inequality and does not require disjointifying the given family.")),
                Paragraph(Text(
                    "This criterion follows from the intersection result and the native sum, basis, cardinality, comap, free-matroid and restriction facts above. The uniform construction uses Fin k throughout, so k = 0 and the empty ground are included: with no slots the union is empty, and the subset inequalities force the ground to be empty; an empty ground admits empty slots for every k. A loop in a nonempty ground violates the inequality on its singleton, whose cardinality is one and rank is zero. Thus nonempty rank-zero grounds fail the criterion as well. The same construction treats all these cases without a positive-k or loopless premise."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var statement = And(Attaining(), UpperBound());
        statement = Imp(Equal(Ground("M2"), V("E")), statement);
        statement = Imp(Equal(Ground("M1"), V("E")), statement);
        statement = All("M2", MatroidType, statement);
        statement = All("M1", MatroidType, statement);
        statement = Imp(A(Q("Set", "Finite"), V("E")), statement);
        statement = All("E", SetType, statement);
        return All("alpha", new Formula.Subscript(V("Type"), V("u")), statement);
    }

    private static Formula Attaining()
    {
        var equality = Equal(Card("I"), RankSum("X"));
        var clauses = And(Subset("I", "E"), And(Subset("X", "E"),
            And(Indep("M1", "I"), And(Indep("M2", "I"), equality))));
        return Some("I", SetType, Some("X", SetType, clauses));
    }

    private static Formula UpperBound() => All("J", SetType, All("Y", SetType,
        Imp(Indep("M1", "J"), Imp(Indep("M2", "J"),
            new Formula.Relation(Card("J"), FormulaRelationOperator.LessThanOrEqual, RankSum("Y"))))));

    private static Formula RankSum(string cut) => Seq(
        Rank("M1", V(cut)), Sp, Plus, Sp,
        Rank("M2", Parenthesized(Seq(V("E"), Sp, Setminus, Sp, V(cut)))));
    private static Formula Rank(string matroid, Formula set) =>
        A(Q("ENat", "toNat"), A(Q("Matroid", "eRk"), V(matroid), set));
    private static Formula Ground(string matroid) => A(Q("Matroid", "E"), V(matroid));
    private static Formula Indep(string matroid, string set) => A(Q("Matroid", "Indep"), V(matroid), V(set));
    private static Formula Card(string set) => A(Q("Set", "ncard"), V(set));
    private static Formula Subset(string a, string b) =>
        new Formula.Relation(V(a), FormulaRelationOperator.SubsetOf, V(b));
    private static Formula SetType => A(V("Set"), V("alpha"));
    private static Formula MatroidType => A(V("Matroid"), V("alpha"));
    private static Formula V(string name) => F.Id(name);
    private static Formula A(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Q(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Parenthesized(Formula formula) => Seq(Open, formula, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}

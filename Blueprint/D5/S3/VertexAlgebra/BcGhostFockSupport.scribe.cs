using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostFockSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostFockSupport.";
    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Z() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Bound() => Call("cutoff", F.Id("m"), F.Id("v"));
    private static Formula Pair() => Call("N", Seq(F.Id("m"), Plus, F.Id("k")),
        Seq(Minus, F.Id("k")), F.Id("v"));
    private static Formula Rings() => Seq(Forall, Sp, F.Id("K"), Colon, Call("Type"), Comma,
        OpenBracket, Call("CommRing", F.Id("K")), CloseBracket, Comma, Esc);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed finite-subset ghost operators admit statewise finite normal ordering on an infinite algebraic Fock space.",
        H("Infinite bc Fock states and normal ordering"),
        Blocks(
            Paragraph(Text("Let K be any commutative ring and let F be the free K-module on "
                + "all finite subsets of the natural numbers. A state is a finite superposition "
                + "of these subsets; there is no global bound on the available sites. The vacuum "
                + "is the basis vector of the empty subset. At site i, insertion vanishes when "
                + "i is present, while deletion vanishes when i is absent. Both nonzero actions "
                + "carry the sign (-1) raised to the number of occupied sites smaller than i.")),
            Paragraph(Text("For m <= -2, b_m inserts the even site 2(-m-2); otherwise it "
                + "deletes the odd site 2(m+1)+1. For n <= 1, c_n inserts the odd site "
                + "2(1-n)+1; otherwise it deletes the even site 2(n-2). The normal-ordered "
                + "pair N(p,q) is b_p composed with c_q for p <= -2, and minus c_q composed "
                + "with b_p otherwise. Products act on the rightmost state first.")),
            Paragraph(Text("These are the untwisted weight-(2,-1) mode conventions associated "
                + "with lambda=-1 in Eholzer, Feher and Honecker, Ghost Systems: A Vertex "
                + "Algebra Point of View, Section 2. Relative to their mathematical modes "
                + "in (2.7)-(2.10), b_m is b at index m+1 and c_n is c at index n-2. The "
                + "b-mode split at mathematical index zero becomes p <= -2, and the "
                + "c-mode split becomes n <= 1. After the paper's fermionic reordering, "
                + "the coefficient in (2.15) becomes m-k. This is a comparison of "
                + "conventions, not a proved equality with the paper's stress tensor. "
                + "The present assertions concern the concrete operators and "
                + "their support and generation; they do not assert canonical anticommutation "
                + "relations, the Virasoro relation, a vertex algebra or a BRST complex.")),
            Describe.Lean(
                DescribeId.Create("annihilate-unoccupied-site"),
                DeclarationHandle.Create(Prefix + "annihilate_eq_zero"),
                H("An unoccupied site annihilates the whole superposition"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("v"),
                    InMacro, Sp, F.Id("F"), Comma, F.Id("i"), InMacro, Sp, N(), Comma, Esc,
                    Neg, Open, F.Id("i"), InMacro, Sp, Call("occupied", F.Id("v")), Close,
                    Sp, Rightarrow, Sp, Call("annihilate", F.Id("i"), F.Id("v")), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The occupied set is the union of all finite subsets "
                    + "in the Finsupp support of v. If i is outside this union, deletion at "
                    + "i vanishes on each basis state appearing with nonzero coefficient, "
                    + "and linear extension gives zero on the entire state. The "
                    + "supremum-tail lemma uses this statement directly; through that "
                    + "lemma it also supplies both tails of the normal-ordering interval. "
                    + "It is available directly for statewise b- and c-annihilator bounds."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("annihilate-above-occupied-supremum"),
                DeclarationHandle.Create(Prefix + "annihilate_eq_zero_of_sup_lt"),
                H("Deletion above every occupied site vanishes"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("v"),
                    InMacro, Sp, F.Id("F"), Comma, F.Id("i"), InMacro, Sp, N(), Comma, Esc,
                    Call("sup", Call("occupied", F.Id("v")), F.Id("id")), Lt, Sp,
                    F.Id("i"), Sp, Rightarrow, Sp,
                    Call("annihilate", F.Id("i"), F.Id("v")), Eq, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supremum is taken in the natural numbers "
                    + "using id, and is zero for the empty occupied set. Every occupied "
                    + "site is at most this supremum, so a strictly larger site is absent "
                    + "and the preceding deletion lemma applies. Both the lower c-tail "
                    + "and the upper b-tail in normal_pair_support_interval consume this "
                    + "bound. Applied to a shifted state, it bounds the corresponding "
                    + "row without requiring one global cutoff for all Fock states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normal-pair-support-interval"),
                DeclarationHandle.Create(Prefix + "normal_pair_support_interval"),
                H("A state determines a finite normal-ordering interval"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("m"),
                    InMacro, Sp, Z(), Comma, F.Id("v"), InMacro, Sp, F.Id("F"), Comma, Esc,
                    Call("supp", Seq(F.Id("k"), Mapsto, Pair())), Sp, Subseteq, Sp,
                    OpenBracket, Minus, Bound(), Comma, Bound(), CloseBracket))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let M(v) be the largest occupied site among all subsets "
                    + "in the support of v, with value zero for the empty union. The bound is "
                    + "cutoff(m,v)=M(v)+|m|+4. For a sufficiently negative k, the rightmost "
                    + "c-mode deletes an even site above M(v). For a sufficiently positive k, "
                    + "normal ordering puts a b-annihilator at an odd site above M(v) on the "
                    + "right. Both tails therefore vanish on the given state. Finite support "
                    + "is established separately for each input, and is not assumed of the "
                    + "operator-valued family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("stress-tensor-interval-sum"),
                DeclarationHandle.Create(Prefix + "L_interval_sum"),
                H("The linear stress-tensor candidate has an interval formula"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("m"), Comma,
                    F.Id("a"), Comma, F.Id("z"), InMacro, Sp, Z(), Comma, F.Id("v"),
                    InMacro, Sp, F.Id("F"), Comma, Esc,
                    F.Id("a"), Leq, Sp, Minus, Bound(), Sp, Land, Sp,
                    Bound(), Leq, Sp, F.Id("z"), Sp, Rightarrow, Sp,
                    Call("L", F.Id("m"), F.Id("v")), Eq, Sum,
                    Underscore, Grp(F.Id("k"), Eq, F.Id("a")), Caret, Grp(F.Id("z")),
                    Open, F.Id("m"), Minus, F.Id("k"), Close, Pair()))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("L_m(v) is the pointwise finite sum of (m-k)N(m+k,-k)v. "
                    + "The scalar is the integer m-k mapped into K. Additivity follows by "
                    + "combining the two finite input supports, and scalar compatibility "
                    + "follows from the finite-sum scalar identity. Every closed integer "
                    + "interval [a,z] enclosing the explicit bound "
                    + "[-cutoff(m,v),cutoff(m,v)] computes exactly the same action. "
                    + "The hypotheses are a <= -cutoff(m,v) and cutoff(m,v) <= z; "
                    + "enclosing only the actual support is not this theorem's premise."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("creation-cyclic"),
                DeclarationHandle.Create(Prefix + "creation_cyclic"),
                H("Creation modes generate all finite superpositions"),
                StatementSource.FromAuthor(Disp(Seq(Rings(), Forall, Sp, F.Id("W"),
                    InMacro, Sp, Call("Submodule", F.Id("K"), F.Id("F")), Comma, Esc,
                    F.Id("vacuum"), InMacro, Sp, F.Id("W"), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("m"), InMacro, Sp, Z(), Comma, Sp,
                    F.Id("m"), Leq, Sp, Minus, D(2), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("v"), InMacro, Sp, F.Id("W"), Comma,
                    Call("b", F.Id("m"), F.Id("v")), InMacro, Sp, F.Id("W"), Close,
                    Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("n"), InMacro, Sp, Z(), Comma, Sp,
                    F.Id("n"), Leq, Sp, D(1), Sp, Rightarrow, Sp,
                    Forall, Sp, F.Id("v"), InMacro, Sp, F.Id("W"), Comma,
                    Call("c", F.Id("n"), F.Id("v")), InMacro, Sp, F.Id("W"), Close,
                    Sp, Rightarrow, Sp, F.Id("W"), Eq, Call("top")))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/VertexAlgebra/eholzer1997ghost")),
                Blocks(Paragraph(Text("Every even insertion is a b-creation mode and every "
                    + "odd insertion is a c-creation mode. Induction on a finite subset "
                    + "constructs its basis vector from the vacuum. The insertion coefficient "
                    + "is a sign whose square is one, so it can be removed over any "
                    + "commutative ring, including characteristic two. Linear induction then "
                    + "generates every finite superposition. The classical Fock basis is "
                    + "described in Section 2, equations (2.9)-(2.10), of the cited paper."))),
                DescribeRole.Theorem))));
}

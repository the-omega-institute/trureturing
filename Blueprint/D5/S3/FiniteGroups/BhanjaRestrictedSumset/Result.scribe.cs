using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.BhanjaRestrictedSumset;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/FiniteGroups/BhanjaRestrictedSumset/Result.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bhanja2025distinctterms");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd restricted sumsets in elementary abelian 2-groups have smaller minima.",
        H("Minima with at most two distinct summands"), Blocks(
            Describe.Lean(DescribeId.Create("h-sumset"),
                DeclarationHandle.Create(Owner + "hSumset"),
                H("Ordinary h-fold sumset"), StatementSource.FromAuthor(Disp(Group(All("h", N, All("A", FS(G), Eq(Call("hSumset", h, A), Smul(h, A))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The ordinary sumset is the existing pointwise natural scalar action on finsets."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restricted-sumset"),
                DeclarationHandle.Create(Owner + "restrictedSumset"),
                H("At most r different summands"), StatementSource.FromAuthor(Disp(Group(All("h", N, All("r", N, All("A", FS(G), RestrictedDefinition())))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("§4, “Further Remarks”, printed p. 11: “Another sumset that may come immediately to the reader’s mind is the sumset h(≤r) A, which contains those elements of the group G that are the sum of h elements of A with at most r distinct elements.” The superscript appears as (≤r) in the text extraction. The finite image counts different values, allowing repetitions and allowing fewer than r values. Functions are enumerated by Fintype.piFinset, filtered by that cardinality and mapped to their sums."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restricted-membership"),
                DeclarationHandle.Create(Owner + "memR"),
                H("Function characterization of restricted sums"), StatementSource.FromAuthor(Disp(Group(All("h", N, All("r", N, All("A", FS(G), All("x", G, MemRBody()))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Membership in the filtered finite function space gives precisely the membership and image-cardinality conditions. This characterization is used to prove the restricted identity."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("double-zero"),
                DeclarationHandle.Create(Owner + "doubleZero"),
                H("Twice every vector is zero"), StatementSource.FromAuthor(Disp(All("m", N, All("a", E, Eq(Smul(D(2), V("a")), D(0)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("ZModModule.char_nsmul_eq_zero gives the characteristic-two identity for this module over ZMod 2."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("odd-scalar"),
                DeclarationHandle.Create(Owner + "oddSmul"),
                H("Odd repetition recovers the vector"), StatementSource.FromAuthor(Disp(All("m", N, All("h", N, Imp(Call("Odd", h), All("a", E, Eq(Smul(h, V("a")), V("a")))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The scalar coefficient reduces modulo two. Odd coefficients have remainder one. Constant functions therefore recover every member of A."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pair-sum"),
                DeclarationHandle.Create(Owner + "pairSum"),
                H("An odd sum of two possible values is one of them"), StatementSource.FromAuthor(Disp(All("m", N, All("h", N, Imp(Call("Odd", h), All("f", Arrow(Fin(h), E), All("a", E, All("b", E, Imp(All("i", Fin(h), Or(Eq(App(f, V("i")), V("a")), Eq(App(f, V("i")), V("b")))), Or(Eq(SumF(), V("a")), Eq(SumF(), V("b")))))))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Partition the indices according to f i = a. The two multiplicities add to h, so exactly one is odd. Reducing both scalar coefficients modulo two gives one of a and b."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("restricted-odd"),
                DeclarationHandle.Create(Owner + "restrictedOdd"),
                H("The restricted odd sumset equals A"), StatementSource.FromAuthor(Disp(All("m", N, All("h", N, Imp(Call("Odd", h), All("A", FS(E), Eq(Call("restrictedSumset", h, D(2), A), A))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The nonempty image of a function of odd positive length has cardinality one or two. In the singleton case its sum is that value; in the pair case pairSum gives one of the values. Conversely a constant function realizes every member of A."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("large-double"),
                DeclarationHandle.Create(Owner + "largeDouble"),
                H("More than half the group gives every pair sum"), StatementSource.FromAuthor(Disp(Group(All("A", FS(G), Imp(Lt(Call("Fintype.card", G), Mul(D(2), Card(A))), Eq(Add(A, A), U))), true))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For each g the image of A under a ↦ g−a has the same cardinality as A. Finset.inter_nonempty_of_card_lt_card_add_card gives an intersection with A, hence a representation of g as two members of A."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("large-iterated"),
                DeclarationHandle.Create(Owner + "largeIterated"),
                H("Cardinality growth gives all longer sumsets"), StatementSource.FromAuthor(Disp(Group(All("h", N, Imp(Le(D(2), h), All("A", FS(G), Imp(Lt(Call("Fintype.card", G), Mul(D(2), Card(A))), Eq(Call("hSumset", h, A), U))))), true))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The pair sumset is the whole group. For h≥2, Finset.card_nsmul_mono bounds its cardinality by that of h•A, while Finset.card_le_univ bounds the latter by the group order. Finset.eq_univ_of_card gives the equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elementary-gap"),
                DeclarationHandle.Create(Owner + "elementary_two_group_gap"),
                H("The elementary 2-group family"), StatementSource.FromAuthor(Disp(Family(false))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For m≥2 and a subset in the strict half-to-full range, restrictedOdd gives the restricted identity and largeIterated gives the ordinary identity. The upper endpoint is retained to describe the strict-gap range; the ordinary covering identity itself only needs the lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ordinary-minimum"),
                DeclarationHandle.Create(Owner + "minSize"),
                H("Minimum ordinary cardinality"), StatementSource.FromAuthor(Disp(Group(All("k", N, All("h", N, Eq(Call("minSize", G, V("k"), h), Minimum(false))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The natural-number infimum runs over cardinalities of ordinary sumsets for every k-element finset. When a k-element finset exists, the nonempty set of natural numbers has a least element."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("restricted-minimum"),
                DeclarationHandle.Create(Owner + "minRestrictedSize"),
                H("Minimum restricted cardinality"), StatementSource.FromAuthor(Disp(Group(All("k", N, All("h", N, All("r", N, Eq(Call("minRestrictedSize", G, V("k"), h, r), Minimum(true)))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The same minimization is performed for the at-most-r-distinct sumset. Both minima optimize over all k-element subsets, not just a selected witness."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("question-claim"),
                DeclarationHandle.Create(Owner + "claim"),
                H("The equality asked in Question 1"), StatementSource.FromAuthor(Disp(Eq(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("§4, “Further Remarks”, printed p. 11: “Question 1. Is it always the case that the minimum size of both the sumsets hA and h(≤r) A are the same in any abelian group G, where the minimum runs over the subsets of G of size (say) k?” The preceding sentence specifies r ≥ 2. The claim uses h ≥ 1 and an attainable cardinality k, quantifies over all abelian groups in Type, and compares the two natural-number minima. Allowing k=0 adds a true empty-set case; the refutation uses k=3."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("uniform-minimum"),
                DeclarationHandle.Create(Owner + "uniformMinimum"),
                H("A constant cardinality determines the minimum"), StatementSource.FromAuthor(Disp(UniformBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If every k-element finset has the same image cardinality v and one such finset exists, the set of cardinalities is the singleton {v}; its infimum is v. This is used for both minima."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("elementary-minima"),
                DeclarationHandle.Create(Owner + "elementary_two_group_minima"),
                H("Exact minima throughout the family"), StatementSource.FromAuthor(Disp(Family(true))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("There exists a k-element subset since k<2^m. The two identities for every such subset make the respective cardinality sets {k} and {2^m}. Thus the minima are k and 2^m, with a strict inequality in the given range."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("question-refutation"),
                DeclarationHandle.Create(Owner + "result"),
                H("Question 1 has a negative answer"), StatementSource.FromAuthor(Disp(new Formula.Not(V("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("At m=2, h=3, k=3 and r=2, the two exact minima are 3 and 4. Their equality would imply 3=4. The general family establishes both minima before this specialization."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bhanja-2025-restricted-sumset-question"),
                    ResolutionKind.Refuted)))));

    private static Formula V(string s) => F.Id(s);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula G => V("G");
    private static Formula h => V("h");
    private static Formula r => V("r");
    private static Formula A => V("A");
    private static Formula f => V("f");
    private static Formula U => Call("Finset.univ");
    private static Formula E => Arrow(Fin(V("m")), Call("ZMod", D(2)));
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula Arrow(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula App(Formula x, params Formula[] args) => new Formula.Apply(x, [.. args]);
    private static Formula Call(string name, params Formula[] args)
    {
        var words = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (words.Count > 0) words.Add(Dot);
            words.Add(V(word));
        }
        return App(Seq(Operatorname, Grp([.. words])), args);
    }
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula FS(Formula g) => Call("Finset", g);
    private static Formula Card(Formula x) => Call("Finset.card", x);
    private static Formula Smul(Formula x, Formula y) => Call("HSMul.hSMul", x, y);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.And, P(y));
    private static Formula Or(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Or, P(y));
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Implies, P(y));
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(P(x), FormulaLogicOperator.Iff, P(y));
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(P(x), y);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Inst(string n) => Seq(OpenBracket, Call(n, G), CloseBracket, Sp);
    private static Formula Group(Formula body, bool finite = false) => All("G", Seq(V("Type"), Star),
        finite ? Seq(Inst("AddCommGroup"), Inst("DecidableEq"), Inst("Fintype"), body) : Seq(Inst("AddCommGroup"), Inst("DecidableEq"), body));
    private static Formula Lam(string n, Formula t, Formula body) =>
        Seq(LambdaLower, Sp, P(Seq(V(n), Colon, Sp, t)), Sp, Mapsto, Sp, P(body));
    private static Formula RestrictedDefinition() => Eq(Call("restrictedSumset", h, r, A),
        Call("Finset.image", Lam("f", Arrow(Fin(h), G), SumF()),
            Call("Finset.filter", Lam("f", Arrow(Fin(h), G), Le(ImageCard(), r)),
                Call("Fintype.piFinset", Call("Function.const", Fin(h), A)))));
    private static Formula SumF() => Seq(new Formula.Subscript(Sum, Seq(V("i"), Colon, Sp, Fin(h))), Sp, App(f, V("i")));
    private static Formula ImageCard() => Card(Call("Finset.image", f, U));
    private static Formula AllValues() => All("i", Fin(h), Mem(App(f, V("i")), A));
    private static Formula MemRBody() => Iff(Mem(V("x"), Call("restrictedSumset", h, r, A)),
        Ex("f", Arrow(Fin(h), G), And(AllValues(), And(Le(ImageCard(), r), Eq(SumF(), V("x"))))));
    private static Formula Builder(Formula body) => Seq(OpenBrace, V("n"), Colon, Sp, N, Sp, Bar, Sp, P(body), CloseBrace);
    private static Formula Minimum(bool restricted) => Call("sInf", Builder(
        Ex("A", FS(G), And(Eq(Card(A), V("k")), Eq(Card(restricted
            ? Call("restrictedSumset", h, r, A) : Call("hSumset", h, A)), V("n"))))));
    private static Formula ClaimBody() => All("G", V("Type"), Seq(Inst("AddCommGroup"), Inst("DecidableEq"),
        All("h", N, All("k", N, All("r", N, Imp(Le(D(1), h), Imp(Le(D(2), r),
            Imp(Ex("A", FS(G), Eq(Card(A), V("k"))), Eq(Call("minRestrictedSize", G, V("k"), h, r), Call("minSize", G, V("k"), h))))))))));
    private static Formula Family(bool minima)
    {
        var k = minima ? V("k") : Card(A);
        var conclusion = minima
            ? And(Eq(Call("minRestrictedSize", E, k, h, D(2)), k), Eq(Call("minSize", E, k, h), Pow(D(2), V("m"))))
            : And(Eq(Call("restrictedSumset", h, D(2), A), A), Eq(Call("hSumset", h, A), U));
        var range = Imp(Lt(Pow(D(2), Sub(V("m"), D(1))), k), Imp(Lt(k, Pow(D(2), V("m"))), conclusion));
        return All("m", N, Imp(Le(D(2), V("m")), All("h", N, Imp(Call("Odd", h), Imp(Le(D(3), h),
            minima ? All("k", N, range) : All("A", FS(E), range))))));
    }
    private static Formula UniformBody()
    {
        var hypothesis = All("A", FS(G), Imp(Eq(Card(A), V("k")), Eq(Card(App(V("F"), A)), V("v"))));
        var minimum = Call("sInf", Builder(Ex("A", FS(G), And(Eq(Card(A), V("k")), Eq(Card(App(V("F"), A)), V("n"))))));
        return All("G", Seq(V("Type"), Star), Seq(Inst("DecidableEq"), All("k", N, All("v", N,
            All("F", Arrow(FS(G), FS(G)), Imp(Ex("A", FS(G), Eq(Card(A), V("k"))), Imp(hypothesis, Eq(minimum, V("v")))))))));
    }
}

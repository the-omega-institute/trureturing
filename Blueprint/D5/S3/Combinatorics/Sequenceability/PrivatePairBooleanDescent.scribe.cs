using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;
internal sealed class PrivatePairBooleanDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact Boolean coverage descent at a private pair",
        H("Exact Boolean coverage descent at a private pair"), Blocks(
        Describe.Lean(DescribeId.Create("infix-separator"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.infix_avoid_separator"),
            H("An interval avoiding a separator lies on one side"),
            StatementSource.FromAuthor(SeparatorStatement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For arbitrary lists l,r,t and a coordinate a, if t is an interval of l ++ a::r and does not contain a, then t is an interval of l or r. This includes the empty interval. No decidable equality or duplicate-free premise is required."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("main-result"),
            DeclarationHandle.Create("D5/S3/Combinatorics/Sequenceability/PrivatePairBooleanDescent.private_pair_exact_boolean_descent"),
            H("A private pair preserves every reduced permutation"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("M is an integer submodule of functions on the unchanged original indices. "
                + "Complete M E consists of all nonempty proper subsets of the finite original ground set E whose coefficient-one Boolean rows lie in M. "
                + "Covers quantifies over every duplicate-free literal list enumerating E, with an actual nonempty proper contiguous interval. "
                + "Minimal is inclusion minimality in that complete family. Only the selected support S has cardinality at least three; "
                + "the other minimal supports can have arbitrary cardinalities. The distinct original indices u,v lie in S and in no other minimal member."))),
            DescribeRole.Theorem),
        Paragraph(Text("For a row A containing a private index, choose a minimal nonempty Boolean row B inside A. "
            + "If B contains that index, privacy identifies B with S. Otherwise subtract its actual Boolean row and recurse on A minus B. "
            + "The strict finite descent proves S is contained in A. Thus every complete row meeting u or v contains u,v and an actual retained x in S minus {u,v}. "
            + "All larger mixed rows remain in scope.")),
        Paragraph(Text("Write Y = E minus {u,v}. For each given reduced order b, split on actual membership of row Y in M. "
            + "If it is absent, apply original coverage to (u,b,v). A covering row meeting the deleted pair contains both endpoints and is full, a contradiction. "
            + "An avoiding row is an interval of b, and cannot be full Y by the membership split.")),
        Paragraph(Text("If row Y belongs to M, rotate the given b just after x, obtaining (c1,...,x), and apply original coverage to (u,c1,v,c2,...,x). "
            + "A row meeting the pair contains both endpoints u,x and is full. An avoiding row lies inside one of two proper pieces. "
            + "The existing ZeroTotalCircleGood.rotated_two_runs supplier makes either that run or its complement an interval of the SAME original b. "
            + "The exact identity row(complement) = row(Y) - row(run) gives membership in M. Both witnesses are nonempty and proper; "
            + "full Y is excluded even in this second case. The reduced length two boundary is included.")),
        Paragraph(Text("The reducedSpan definition is exactly the integer span of ALL proper reduced Boolean rows whose extension by zero belongs to M. "
            + "Its image under embed lies in M. Conversely every nonempty proper reduced Boolean row with image in M is a generator, "
            + "so this is its complete proper Boolean family. Extension sends a unit and a difference to the same coefficient-one original coordinate vectors. "
            + "No equality with an intersection lattice, rational saturation, division, original total-sum or torsion assumption is asserted.")),
        Paragraph(Text("For the original source family H, instantiate M with Submodule.span over integer Boolean rows of H. "
            + "Original H coverage implies Covers because each source row is a generator. Each output image in M therefore has finite ORIGINAL-H integer coefficients, "
            + "by Mathlib's Submodule.mem_span_image_finset_iff_exists_fun. For an original interval source A, the direct witness has its original generator coefficients; "
            + "the complement witness subtracts those coefficients from an actual certificate for row Y. Finite linear combinations compose these coefficients. "
            + "This exact application is compiled transiently rather than retained as a named binding theorem.")),
        Paragraph(Text("This is a repository-derived descent lemma. The unrestricted original connector, Good and adaptive merge statements remain open. "
            + "No forest constructor or literature-priority claim is part of this delivery.")) )));

    private static Formula SeparatorStatement()
    {
        var x=Id("X");var a=Id("a");var t=Id("t");var l=Id("l");var r=Id("r");
        return FormulaDsl.Disp(All("X",Call("Type"),All("a",x,All("t",Call("List",x),
            All("l",Call("List",x),All("r",Call("List",x),Implies(
                Both(Call("IsInfix",t,Call("append",l,Call("cons",a,r))),
                    new Formula.Not(new Formula.Relation(a,FormulaRelationOperator.MemberOf,t))),
                Either(Call("IsInfix",t,l),Call("IsInfix",t,r)))))))));
    }

    private static Formula Statement()
    {
        var x = Id("X"); var m = Id("M"); var e = Id("E"); var s = Id("S");
        var u = Id("u"); var v = Id("v"); var b = Id("B");
        var i = Id("i"); var j = Id("j"); var z = Id("z");
        var y = Call("erase", Call("erase", e, u), v);
        var l = Call("reducedSpan", m, y);
        Formula Member(Formula a, Formula c) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, c);
        Formula Single(Formula a) => Call("single", a, Num(1));
        var privacy = All("B", Call("Finset", x), Implies(
            Both(Call("Minimal", m, e, b), Either(Member(u, b), Member(v, b))), Equal(b, s)));
        var premises = Conjunction(Call("Covers", m, e), Call("Minimal", m, e, s),
            new Formula.Relation(Num(3), FormulaRelationOperator.LessThanOrEqual, Call("card", s)),
            Member(u, s), Member(v, s), NotEqual(u, v), privacy);
        var result = Conjunction(Call("Covers", m, y), Equal(Add(Call("card", y), Num(2)), Call("card", e)),
            All("z", Call("Function", y, new Formula.Integers()),
                Implies(Member(z, l), Member(Call("embed", y, z), m))),
            All("B", Call("Finset", y), Implies(Both(Call("Nonempty", b), NotEqual(b, Call("univ"))),
                Iff(Member(Call("row", b), l), Member(Call("row", Call("image", Call("val"), b)), m)))),
            All("i", y, Equal(Call("embed", y, Single(i)), Single(Call("val", i)))),
            All("i", y, All("j", y,
                Equal(Call("embed", y, Subtract(Single(i), Single(j))),
                    Subtract(Single(Call("val", i)), Single(Call("val", j)))))));
        return FormulaDsl.Disp(All("X", Call("Type"), All("inst", Call("DecidableEq", x),
            All("M", Call("Submodule", new Formula.Integers(), Call("Function", x, new Formula.Integers())),
            All("E", Call("Finset", x), All("S", Call("Finset", x),
            All("u", x, All("v", x, Implies(premises, result)))))))));
    }
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Both(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Either(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Conjunction(params Formula[] terms)
    {
        var result = terms[^1];
        for (var i = terms.Length - 2; i >= 0; i--) result = Both(terms[i], result);
        return result;
    }
}

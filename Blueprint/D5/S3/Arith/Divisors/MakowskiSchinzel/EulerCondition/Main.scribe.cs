using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Divisors.MakowskiSchinzel.EulerCondition;

internal sealed class MakowskiSchinzelEulerMainDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Divisors/MakowskiSchinzel/EulerCondition/Main.";
    private static readonly LibraryNoteRef Cohen =
        LibraryNoteRef.Create("D5/L/ArithUnits/cohen1997makowski");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An Euler-product condition for the sigma-totient inequalities",
        H("An Euler-product condition for the sigma-totient inequalities"), Blocks(
            Describe.Lean(DescribeId.Create("makowski-schinzel-euler-top-group"),
                DeclarationHandle.Create(Prefix + "topGroup"),
                H("Grouping by the largest predecessor prime"),
                StatementSource.FromAuthor(Disp(Group())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The group at r consists of the prime divisors q of n for which r " +
                    "divides q-1 and q-1 is (r+1)-smooth. For an odd prime r this means " +
                    "that r is the largest prime factor of q-1. These groups partition " +
                    "the non-Fermat prime support when r ranges over odd primes."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("euler-condition-mass-common-divisor"),
                DeclarationHandle.Create(
                    Prefix + "mass_le_euler_of_common_dvd"),
                H("A common divisor bounds the reciprocal mass"),
                StatementSource.FromAuthor(Disp(MassStatement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let Q be a finite set of natural numbers. Suppose D divides every " +
                    "predecessor q-1 and each quotient (q-1)/D is nonzero with all prime " +
                    "factors at most r. The mass sum r/(q-1) is bounded by r/D times the " +
                    "Euler product through r. The inequality is strict when r>=2 and D>0. " +
                    "No primality or parity assumption is imposed on q or r.")),
                    Paragraph(Text(
                    "If D=0 the quotient is zero, so Q must be empty. For positive D, " +
                    "the quotient map is injective on Q. Apply the smooth Euler bound " +
                    "to its finite image and multiply by r/D. For r>=2 choose a power " +
                    "of two above every element of the image. It is smooth and missing " +
                    "from the image. Adding its positive reciprocal before applying the " +
                    "same bound proves strictness.")),
                    Paragraph(Text(
                    "Quotient smoothness is weaker than predecessor smoothness: " +
                    "Q={11}, r=2, D=5 has smooth quotient 2 but predecessor 10. Without " +
                    "divisibility, Q={3,4}, r=1, D=2 has smooth quotients 1,1 but " +
                    "mass 5/6 above bound 1/2. Without " +
                    "smoothness, Q={2,3,4,5}, r=2, D=1 has mass 25/6 above bound 4. " +
                    "Equality occurs for Q={D+1}, r=1, D>0, and for Q empty, D=0; " +
                    "r=0 also gives equality."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("euler-condition-labelled-groups"),
                DeclarationHandle.Create(Prefix + "one_le_psi_of_labelled_groups"),
                H("Labelled groups and actual odd valuations"),
                StatementSource.FromAuthor(Disp(LabelledGroups())),
                AssessedProvenance.FromRepo(Cohen),
                Blocks(Paragraph(Text(
                    "Let Q be the non-Fermat prime support and U its odd predecessor " +
                    "part. Assign each q an arbitrary natural-number label. If every " +
                    "label fibre has product q/(q-1) at most geom(p,v_p(U)), then " +
                    "psi(n)>=1. Factor the full product into its label fibres, apply " +
                    "the local bounds, and identify the resulting geometric product " +
                    "with the abundancy of the selected full valuation components. " +
                    "Their product divides U. Abundancy monotonicity and cancellation " +
                    "of the Euler factors give the conclusion. In fact the local " +
                    "product condition alone suffices: a nonempty fibre has product " +
                    "strictly above one, so its label has positive valuation in U. " +
                    "It is therefore an odd prime dividing U. Divisibility of each " +
                    "individual predecessor by its assigned label is unnecessary. " +
                    "In the comparison with Cohen's condition below, labels are " +
                    "assumed to divide their assigned predecessors.")),
                    Paragraph(Text(
                    "This repository-derived criterion generalizes the group condition " +
                    "of Cohen 1997 Theorem 3, described in Library/ArithUnits/" +
                    "cohen1997makowski.md: the latter uses group cardinality instead " +
                    "of the full valuation. Every assigned member contributes to that " +
                    "valuation, and the geometric sum is monotone. The capacity form " +
                    "sum p/(q-1)<=1 implies Cohen's group-product bound by the " +
                    "mass-product inequality necessary_mass, and hence implies this " +
                    "criterion. The global condition psi(n)>=1 can instead be used " +
                    "directly with the quantitative sigma-totient theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("makowski-schinzel-euler-condition"),
                DeclarationHandle.Create(Prefix + "makowski_schinzel_of_euler_condition"),
                H("The common-divisor Euler condition"),
                StatementSource.FromAuthor(Disp(Criterion())),
                AssessedProvenance.FromRepo(Cohen),
                Blocks(Paragraph(Text(
                    "For every nonempty group at an odd prime r, suppose its common " +
                    "predecessor divisor is at least r times the Euler product over " +
                    "primes at most r. The smooth reciprocal estimate then bounds the " +
                    "group capacity, the sum of r/(q-1), by one. The finite geometric " +
                    "product inequality converts this capacity into a lower bound for " +
                    "the odd predecessor abundancy. Each group contributes at most the " +
                    "available r-adic valuation, so the product of the geometric factors " +
                    "is at most the abundancy of the odd predecessor part. Consequently " +
                    "psi(n) is at least one, and the quantitative predecessor criterion " +
                    "gives all four displayed inequalities.")),
                    Paragraph(Text(
                    "The statement includes zero and arbitrary prime multiplicities. " +
                    "The factor two is attained at n=2, the odd inequality at n=1, and " +
                    "the non-Fermat hypothesis supplies the strict inequalities. The " +
                    "Euler condition is sufficient rather than necessary: at n=7, the " +
                    "group at r=3 has common predecessor divisor 6, below r E(r)=9, " +
                    "while its capacity is only 1/2. The same proof uses only the weaker " +
                    "capacity condition, the consequence associated with Cohen's " +
                    "1997 result; the displayed theorem retains the explicit Euler " +
                    "and common-divisor condition and applies the labelled-group criterion. " +
                    "Here gcdPredecessor(G) is the gcd " +
                    "of q-1 over q in G, with value zero for the empty group.")),
                    Paragraph(Text(
                    "The literature comparison covers Cohen (1997), " +
                    "Pomerance (1989), Ford (2001/02), Grytczuk, Luca and Wójtowicz " +
                    "(2000), Luca and Pomerance (2002), Pomerance (2026), Sándor (2005), " +
                    "and Grytczuk (2013); the full text of Grytczuk, Luca and Wójtowicz " +
                    "(2001) is unavailable in this comparison."))), DescribeRole.Theorem))));

    private static Formula MassStatement()
    {
        var q = V("q"); var r = V("r"); var d = V("D"); var set = V("Q");
        var pred = Sub(q, D(1));
        var divisibility = All("q", Nat(), Imp(Mem(q, set), Call("dvd", d, pred)));
        var smoothness = All("q", Nat(), Imp(Mem(q, set),
            Mem(Call("natDiv", pred, d), Call("smoothNumbers", Add(r, D(1))))));
        var mass = Sum("q", set, Div(r, pred));
        var euler = Prod("p", Call("primesLE", r), Div(V("p"), Sub(V("p"), D(1))));
        var bound = Mul(Div(r, d), euler);
        return All("Q", Call("Finset", Nat()), All("r", Nat(), All("D", Nat(),
            Imp(divisibility, Imp(smoothness, And(Le(mass, bound),
                Imp(Le(D(2), r), Imp(Lt(D(0), d), Lt(mass, bound)))))))));
    }

    private static Formula LabelledGroups()
    {
        var n = V("n"); var q = V("q"); var seed = V("a"); var label = V("label");
        var set = Call("nonFermatFactors", n);
        var group = Call("filterLabel", set, label, Call("label", seed));
        var local = All("a", Nat(), Imp(Mem(seed, set),
            Le(Prod("q", group, Div(q, Sub(q, D(1)))),
                Call("geom", Call("label", seed),
                    Call("factorization", Call("oddPredecessorPart", n),
                        Call("label", seed))))));
        return All("n", Nat(), All("label", new Formula.TypeArrow(Nat(), Nat()),
            Imp(local, Le(D(1), Call("psi", n)))));
    }

    private static Formula Group()
    {
        var n = V("n"); var r = V("r"); var q = V("q");
        var rhs = And(Mem(q, Call("primeSources", n, r)),
            Mem(Sub(q, D(1)), Call("smoothNumbers", Add(r, D(1)))));
        return All("n", Nat(), All("r", Nat(), All("q", Nat(),
            new Formula.Logic(Mem(q, Call("topGroup", n, r)), FormulaLogicOperator.Iff, rhs))));
    }

    private static Formula Criterion()
    {
        var n = V("n"); var r = V("r"); var p = V("p");
        var group = Call("topGroup", n, r);
        var euler = Prod("p", Call("primesLE", r), Div(p, Sub(p, D(1))));
        var condition = All("r", Nat(), Imp(Call("Prime", r), Imp(Call("Odd", r),
            Imp(Call("Nonempty", group), Le(Mul(r, euler), Call("gcdPredecessor", group))))));
        var sigma = Call("sigma", D(1), Call("totient", n));
        var odd = Call("Odd", n);
        var strict = Imp(Call("Nonempty", Call("nonFermatFactors", n)),
            And(Lt(n, Mul(D(2), sigma)), Imp(odd, Lt(n, sigma))));
        var conclusion = And(Le(n, Mul(D(2), sigma)),
            And(Imp(odd, Le(n, sigma)), strict));
        return All("n", Nat(), Imp(condition, conclusion));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Mem(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
    private static Formula Prod(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(F.Prod, Seq(V(name), Sp, InMacro, Sp, set)),
            Sp, Seq(Open, body, Close));
}

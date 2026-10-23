using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Solitons;

internal sealed class LotkaVolterraIntegralBirationalityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Solitons/LotkaVolterraIntegralBirationality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FluidDynamics/marquette2026lotkavolterra");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In every dimension at least two over a characteristic-zero field, the specified Lotka–Volterra integrals and the last coordinate generate the rational function field.",
        H("Rational reconstruction from the Lotka–Volterra integrals"),
        Blocks(
            Paragraph(Text(
                "Coordinates have indices starting at zero: x(F,n,i) is the source coordinate "
                    + "x with index i+1. Integral indices start at one. Write m = half(n); "
                    + "the source uses n = 2m−1 in the odd case and n = 2m in the even case. "
                    + "All index arithmetic is in the natural numbers, with subtraction truncated "
                    + "at zero. Empty sums are zero and empty products are one. Division in the "
                    + "function field is total, with inverse of zero equal to zero.")),
            Node("function-field", "The rational function field", "FunctionField", FunctionFieldFormula(),
                "Take the fraction field of the polynomial ring on Fin(n), the set of indices "
                    + "from zero to n−1. The coefficient field is arbitrary and n may be zero.",
                AssessedProvenance.FromRepo()),
            Node("x", "The coordinate functions", "x", CoordinateFormula(),
                "For i < n, X_i denotes the polynomial indeterminate at the corresponding "
                    + "element of Fin(n), and algebraMap is the canonical map from the polynomial "
                    + "ring to its fraction field. Thus x(F,n,i) is the source's x_{i+1}. "
                    + "For every natural i at least n, the coordinate function is defined to be zero.",
                AssessedProvenance.FromRepo()),
            Node("s", "The partial sums", "S", PartialSumFormula(),
                "S(F,n,i) is the sum of the first i coordinates, so it is the source's "
                    + "x_1 + ⋯ + x_i when i ≤ n. It is zero for i = 0 and remains equal "
                    + "to S(F,n,n) for i ≥ n because the remaining coordinates are zero.",
                AssessedProvenance.FromRepo()),
            Node("half", "The number of forward integrals", "half", HalfFormula(),
                "Nat.div is natural-number floor division, giving m = floor((n+1)/2). Hence n = 2m−1 "
                    + "for positive odd n, and n = 2m for even n, including zero.",
                AssessedProvenance.FromRepo()),
            Node("fk", "The forward integrals in both parities", "Fk", ForwardFormula(),
                "Section 3 defines F_k for 1 ≤ k ≤ m. After shifting coordinate indices "
                    + "down by one, the odd factors x_{2s+1}/x_{2s} become "
                    + "x(F,n,2s)/x(F,n,2s−1), and the even factors "
                    + "x_{2s+2}/x_{2s+1} become x(F,n,2s+1)/x(F,n,2s). "
                    + "The finite interval Ico(k,m) contains k ≤ s < m. The displayed "
                    + "definition also specifies Fk for all natural n and k.",
                AssessedProvenance.FromLiterature(Source)),
            Node("gk", "The reversed integrals", "Gk", ReverseFormula(),
                "In Section 3, G_k is obtained from F_k by reversing the n coordinates. "
                    + "For 1 ≤ k ≤ m, its initial sum is S(F,n,n) − S(F,n,2(m−k)), "
                    + "and its product is the prefix of ratios of source odd coordinates "
                    + "to source even coordinates. Reindexing the reversed product gives "
                    + "the same expression in both parities. The total definition uses "
                    + "natural subtraction when k exceeds m.",
                AssessedProvenance.FromLiterature(Source)),
            Node("inputs", "The n rational inputs", "inputs", InputsFormula(),
                "For n ≥ 2, the list begins with F_1 through F_m and ends with the "
                    + "source coordinate x_n = x(F,n,n−1). Between them are G_2 through "
                    + "G_{m−1} when n is odd, and G_1 through G_{m−1} when n is even. "
                    + "There are n entries in either case; an empty middle range contributes "
                    + "no entries. These are the distinct integrals of Section 3, with "
                    + "F_m = G_m equal to the total sum and, in odd dimension, F_1 = G_1. "
                    + "The even list includes G_1, which the list in Appendix A.2 omits. "
                    + "The formula uses v = Fin.val(i), the zero-based value of i, and "
                    + "retains the definition for every n, including zero and one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Generation of the full function field", "claim", ClaimFormula(),
                "The birationality conjecture in Section 2 and Appendix A is expressed "
                    + "as generation of the rational function field by the n specified inputs. "
                    + "The assertion quantifies over every characteristic-zero field and "
                    + "every n ≥ 2. Here top is the full intermediate field inside "
                    + "FunctionField(F,n); no evaluation at a particular coordinate tuple "
                    + "or nonvanishing assumption on such a tuple is imposed.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("lotka-volterra-birationality-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The integrals and last coordinate generate the field"),
                StatementSource.FromAuthor(Disp(Named("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the integrals of Marquette, van der Kamp and Quispel. For the "
                            + "reconstruction, write y_j = x(F,n,j−1) with 1 ≤ j ≤ n, "
                            + "T_i = S(F,n,i), H = T_n, and suppress F and n in Fk and Gk. "
                            + "Thus T_0 = 0 and T_i − T_{i−1} = y_i. Each coordinate and "
                            + "each nonempty consecutive sum of coordinates is a nonzero "
                            + "rational function, by linear independence of polynomial indeterminates.")),
                    Paragraph(Text(
                        "For odd n = 2m−1, put C = F_1 = G_1. Cancellation of products "
                            + "gives F_k G_{m−k}/C = T_{2k−1}(H − T_{2k})/y_{2k} "
                            + "for 1 ≤ k < m, and F_k G_{m−k+1}/C = "
                            + "T_{2k−1}(H − T_{2k−2})/y_{2k−1} for 1 ≤ k ≤ m. "
                            + "Set D_{2k} = F_k G_{m−k}/C and "
                            + "D_{2k−1} = F_k G_{m−k+1}/C − H. These identities give "
                            + "D_i y_i = T_{i−1}(H − T_i). Since G_m = H and G_1 = C, "
                            + "all the D_i needed for 2 ≤ i < n lie in the field of the inputs.")),
                    Paragraph(Text(
                        "Starting at T_{n−1} = H − y_n, recover the partial sums downwards "
                            + "by T_{i−1} = D_i T_i/(H − T_i + D_i), for i = n−1 down to 2. "
                            + "The denominator is nonzero: its product with y_i is "
                            + "(H − T_i)T_i, a product of two nonempty consecutive sums. "
                            + "Differences of consecutive partial sums then recover every coordinate.")),
                    Paragraph(Text(
                        "For even n = 2m with m ≥ 2, write u = y_n and f = F_{m−1}. "
                            + "The second-to-last coordinate is y_{n−1} = u(H − u)/(f + u). "
                            + "The ratio product P = product over 1 ≤ j ≤ m of "
                            + "y_{2j}/y_{2j−1} is u(H + f)/(G_1(H − u)). "
                            + "For 1 ≤ k < m, recover T_{2k} = H F_k/(F_k + P G_{m−k}) "
                            + "and R_k = G_{m−k}/(H − T_{2k}), where R_k is the product "
                            + "over 1 ≤ j ≤ k of y_{2j−1}/y_{2j}. The endpoints are "
                            + "T_0 = 0, T_{2m} = H, R_0 = 1 and R_m = 1/P. "
                            + "Thus r_k = R_k/R_{k−1} is y_{2k−1}/y_{2k}. "
                            + "With q_k = T_{2k} − T_{2k−2}, obtain y_{2k} = q_k/(1+r_k) "
                            + "and y_{2k−1} = q_k − y_{2k}, for 1 ≤ k ≤ m. "
                            + "The denominators are nonzero by the coordinate and consecutive-sum "
                            + "identities. When n = 2, simply use y_1 = H − y_2.")),
                    Paragraph(Text(
                        "In either parity, all coordinates belong to the intermediate field "
                            + "generated by the inputs. This field contains every polynomial in "
                            + "the coordinates and every quotient of such polynomials, so it is "
                            + "the whole rational function field."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("marquette-vanderkamp-quispel-2026-lotka-volterra-birationality"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("lotka-volterra-birationality-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Named(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => At(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Fields(Formula body, bool characteristicZero = false) => Seq(
        Forall, Sp, Typed(F.Id("F"), Seq(Named("Type"), Star)), Sp,
        OpenBracket, Call("Field", F.Id("F")), CloseBracket, Sp,
        characteristicZero
            ? Seq(OpenBracket, Call("CharZero", F.Id("F")), CloseBracket, Sp)
            : Seq(),
        Comma, Sp, Parenthesized(body));
    private static Formula Parameters(Formula body) => Fields(All("n", Naturals(), body));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PolynomialRing() => Call("MvPolynomial", Call("Fin", F.Id("n")), F.Id("F"));
    private static Formula FunctionField() => Call("FunctionField", F.Id("F"), F.Id("n"));
    private static Formula Coordinate(Formula index) => Call("x", F.Id("F"), F.Id("n"), index);
    private static Formula PartialSum(Formula index) => Call("S", F.Id("F"), F.Id("n"), index);
    private static Formula Half() => Call("half", F.Id("n"));
    private static Formula Integral(string name, Formula index) => Call(name, F.Id("F"), F.Id("n"), index);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Twice(Formula value) =>
        new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, Parenthesized(value));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula OddCondition() => Equal(At(Named("Nat", "mod"), F.Id("n"), D(2)), D(1));
    private static Formula EvenCondition() => NotEqual(At(Named("Nat", "mod"), F.Id("n"), D(2)), D(1));
    private static Formula Range(Formula end) => At(Named("Finset", "range"), end);
    private static Formula Interval(Formula start, Formula end) => At(Named("Finset", "Ico"), start, end);
    private static Formula Over(Formula operation, string index, Formula domain, Formula body) => Seq(
        new Formula.Subscript(operation,
            new Formula.Relation(F.Id(index), FormulaRelationOperator.MemberOf, domain)),
        Sp, Parenthesized(body));
    private static Formula Cases(Formula first, Formula firstCondition, Formula second, Formula secondCondition) =>
        Seq(Begin, Grp(F.Id("cases")), first, Amp, firstCondition, RowBreak,
            second, Amp, secondCondition, End, Grp(F.Id("cases")));

    private static Formula FunctionFieldFormula() => Parameters(
        Equal(FunctionField(), Call("FractionRing", PolynomialRing())));

    private static Formula CoordinateFormula()
    {
        Formula i = F.Id("i");
        Formula indeterminate = new Formula.Subscript(F.Id("X"), i);
        Formula image = Call("algebraMap", PolynomialRing(), FunctionField(), indeterminate);
        return Parameters(All("i", Naturals(), Equal(Coordinate(i),
            Cases(image, Less(i, F.Id("n")), D(0), LE(F.Id("n"), i)))));
    }

    private static Formula PartialSumFormula() => Parameters(All("i", Naturals(),
        Equal(PartialSum(F.Id("i")), Over(Sum, "j", Range(F.Id("i")), Coordinate(F.Id("j"))))));

    private static Formula HalfFormula() => All("n", Naturals(),
        Equal(Half(), At(Named("Nat", "div"), Add(F.Id("n"), D(1)), D(2))));

    private static Formula ForwardFormula()
    {
        Formula k = F.Id("k"), s = F.Id("s");
        Formula odd = Multiply(PartialSum(Subtract(Twice(k), D(1))),
            Over(Prod, "s", Interval(k, Half()),
                Fraction(Coordinate(Twice(s)), Coordinate(Subtract(Twice(s), D(1))))));
        Formula even = Multiply(PartialSum(Twice(k)),
            Over(Prod, "s", Interval(k, Half()),
                Fraction(Coordinate(Add(Twice(s), D(1))), Coordinate(Twice(s)))));
        return Parameters(All("k", Naturals(), Equal(Integral("Fk", k),
            Cases(odd, OddCondition(), even, EvenCondition()))));
    }

    private static Formula ReverseFormula()
    {
        Formula remaining = Subtract(Half(), F.Id("k"));
        Formula prefix = Over(Prod, "s", Range(remaining),
            Fraction(Coordinate(Twice(F.Id("s"))), Coordinate(Add(Twice(F.Id("s")), D(1)))));
        return Parameters(All("k", Naturals(), Equal(Integral("Gk", F.Id("k")),
            Multiply(Subtract(PartialSum(F.Id("n")), PartialSum(Twice(remaining))), prefix))));
    }

    private static Formula InputsFormula()
    {
        Formula v = At(Named("Fin", "val"), F.Id("i"));
        Formula afterForward = LE(Half(), v);
        Formula middleCondition = And(afterForward, Less(Add(v, D(1)), F.Id("n")));
        Formula lastCondition = And(afterForward, LE(F.Id("n"), Add(v, D(1))));
        Formula offset = Cases(D(2), OddCondition(), D(1), EvenCondition());
        Formula middleIndex = Add(Parenthesized(Subtract(v, Half())), Parenthesized(offset));
        Formula entries = Seq(Begin, Grp(F.Id("cases")),
            Integral("Fk", Add(v, D(1))), Amp, Less(v, Half()), RowBreak,
            Integral("Gk", middleIndex), Amp, middleCondition, RowBreak,
            Coordinate(Subtract(F.Id("n"), D(1))), Amp, lastCondition,
            End, Grp(F.Id("cases")));
        return Parameters(All("i", Call("Fin", F.Id("n")),
            Equal(Call("inputs", F.Id("F"), F.Id("n"), F.Id("i")), entries)));
    }

    private static Formula ClaimFormula()
    {
        Formula inputRange = At(Named("Set", "range"), Call("inputs", F.Id("F"), F.Id("n")));
        Formula generation = Equal(At(Named("IntermediateField", "adjoin"), F.Id("F"), inputRange), Named("top"));
        Formula assertion = Fields(All("n", Naturals(), Implies(LE(D(2), F.Id("n")), generation)),
            characteristicZero: true);
        return new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff, Parenthesized(assertion));
    }
}

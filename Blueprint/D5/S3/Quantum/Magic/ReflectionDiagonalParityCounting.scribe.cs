using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Magic;

internal sealed class ReflectionDiagonalParityCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Magic/ReflectionDiagonalParityCounting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visiting every nonzero even Boolean label between odd initial and final wire labels requires exponentially many updates and a linear return cost.",
        H("Counting even labels in a CNOT sequence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("update"), DeclarationHandle.Create(Prefix + "update"),
                H("Updating a target label"),
                StatementSource.FromAuthor(Disp(UpdateFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each wire carries a Boolean vector. The ordered pair p specifies the target first and the control second; replace the target label by the sum of those two labels and keep every other label. "
                    + "Addition of Boolean vectors is coordinatewise exclusive-or. The definition is valid for every ordered pair, including equal coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("labels"), DeclarationHandle.Create(Prefix + "labels"),
                H("The final wire labels"),
                StatementSource.FromAuthor(Disp(LabelsFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Starting from ls, apply the updates in the list gs from left to right. The result records every final wire label. "
                    + "No independence or invertibility of the initial label vectors is assumed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("outputs"), DeclarationHandle.Create(Prefix + "outputs"),
                H("The chronological list of target outputs"),
                StatementSource.FromAuthor(Disp(OutputsFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each update, record the new target vector before continuing with the updated wire labels. The empty update list has no outputs. "
                    + "The list retains repeated vectors and has one entry per update; it does not include the initial vectors. "
                    + "A right fold constructs the function of the current label array: each step prepends its target output and passes the updated array to the remaining steps."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("count-bound"), DeclarationHandle.Create(Prefix + "count_bound"),
                H("Visiting all even vectors forces a return cost"),
                StatementSource.FromAuthor(Disp(CountBoundFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume m is positive, every initial and final wire label has odd Boolean coordinate sum, and every nonzero even vector occurs among the target outputs. "
                        + "Exactly half of all Boolean vectors are even: delete a final coordinate, and recover it as the Boolean sum of the remaining coordinates. "
                        + "After removing the zero vector, the number of distinct required vectors bounds the length of the list of even target outputs from below.")),
                    Paragraph(Text(
                        "Call an update with odd target and odd control a birth. Its new target is even. The sums of sublists of the birth outputs include zero and every birth output, are closed under addition, and number at most two raised to the number of birth updates. "
                        + "Induction over the updates shows that every even vector present on a wire or appearing as an output belongs to this span. "
                        + "For an even target output, either both input vectors were even and closure under addition applies, or both were odd and the output is a birth. "
                        + "Since there are no even initial labels and every nonzero even vector appears, the span contains the whole even subspace. Its cardinality bound and strict growth of powers of two force at least m minus one birth updates.")),
                    Paragraph(Text(
                        "Count the wires with even labels. A birth increases this number by one, and an update with even target and odd control decreases it by one; all other combinations of odd and even labels leave it unchanged. "
                        + "Induction gives the exact balance: the final even-wire count plus the number of decreases equals the initial even-wire count plus the number of birth updates. "
                        + "Both endpoint counts are zero, so there are as many decreases as birth updates, hence at least m minus one decreases. "
                        + "Every decrease has an odd target output and is therefore disjoint from the updates counted by even outputs. Adding the two counts gives the displayed lower bound, with subtraction in the natural numbers."))),
                DescribeRole.Theorem))));

    private static Formula UpdateFormula() => All("m", Naturals(), All("ls", LabelArrays(X("m")),
        All("p", Pairs(X("m")), Equal(Local("update", X("ls"), X("p")),
            At(Qualified("Function", "update"), X("ls"), First(X("p")),
                Add(At(X("ls"), First(X("p"))), At(X("ls"), Second(X("p")))))))));

    private static Formula LabelsFormula() => All("m", Naturals(), All("gs", ListOf(Pairs(X("m"))),
        All("ls", LabelArrays(X("m")), Equal(Local("labels", X("gs"), X("ls")),
            At(Qualified("List", "foldl"), Qualified("update"), X("ls"), X("gs"))))));

    private static Formula OutputsFormula()
    {
        Formula empty = Equal(
            Local("outputs", Typed(Qualified("List", "nil"), ListOf(Pairs(X("m"))))),
            At(Qualified("Function", "const"), LabelArrays(X("m")),
                Typed(Qualified("List", "nil"), ListOf(Vectors(X("m"))))));
        Formula step = All("p", Pairs(X("m")), All("gs", ListOf(Pairs(X("m"))),
            All("ls", LabelArrays(X("m")), Equal(Local("outputs", Cons(X("p"), X("gs")), X("ls")),
                Cons(Add(At(X("ls"), First(X("p"))), At(X("ls"), Second(X("p")))),
                    Local("outputs", X("gs"), Local("update", X("ls"), X("p"))))))));
        return All("m", Naturals(), And(empty, step));
    }

    private static Formula CountBoundFormula()
    {
        Formula m = X("m");
        Formula initial = All("j", Fin(m), Equal(SumOver("i", Fin(m), At(X("ls"), X("j"), X("i"))), Qualified("Bool", "true")));
        Formula final = All("j", Fin(m), Equal(SumOver("i", Fin(m),
            At(Local("labels", X("gs"), X("ls")), X("j"), X("i"))), Qualified("Bool", "true")));
        Formula seen = All("v", Vectors(m), Imp(Equal(SumOver("i", Fin(m), At(X("v"), X("i"))), Qualified("Bool", "false")),
            Imp(NE(X("v"), Typed(D(0), Vectors(m))), Mem(X("v"), Local("outputs", X("gs"), X("ls"))))));
        Formula bound = LE(Sub(Add(new Formula.Power(D(2), Sub(m, D(1))), m), D(2)), At(Qualified("List", "length"), X("gs")));
        return All("m", Naturals(), Imp(LT(D(0), m), All("gs", ListOf(Pairs(m)), All("ls", LabelArrays(m),
            Imp(initial, Imp(final, Imp(seen, bound)))))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        Formula value = X(parts[0]);
        for (int i = 1; i < parts.Length; i++) value = Seq(value, Dot, X(parts[i]));
        return Seq(Operatorname, Grp(value));
    }
    private static Formula Local(string name, params Formula[] args) => At(Qualified(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Left, Open, value, Right, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Fin(Formula m) => At(Qualified("Fin"), m);
    private static Formula Vectors(Formula m) => Arrow(Fin(m), Qualified("Bool"));
    private static Formula LabelArrays(Formula m) => Arrow(Fin(m), Vectors(m));
    private static Formula ListOf(Formula type) => At(Qualified("List"), type);
    private static Formula Pairs(Formula m) => Seq(Parenthesized(Fin(m)), Sp, Times, Sp, Parenthesized(Fin(m)));
    private static Formula First(Formula value) => At(Qualified("Prod", "fst"), value);
    private static Formula Second(Formula value) => At(Qualified("Prod", "snd"), value);
    private static Formula Cons(Formula head, Formula tail) => At(Qualified("List", "cons"), head, tail);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(string name, Formula domain, Formula body) => Seq(Forall, Sp, Typed(X(name), domain), Comma, Sp, body);
    private static Formula SumOver(string name, Formula domain, Formula body) => Seq(new Formula.Subscript(Sum, Typed(X(name), domain)), Sp, Parenthesized(body));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
}

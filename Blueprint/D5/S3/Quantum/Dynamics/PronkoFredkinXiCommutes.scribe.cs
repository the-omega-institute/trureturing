using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class PronkoFredkinXiCommutesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Quantum/pronko2025fredkin");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Spin words of the periodic Fredkin chain are read as lattice paths and sorted into Dyck classes. Pronko's diagonal operator Xi weights the balanced classes by alternating signs, and it commutes with the periodic Fredkin Hamiltonian.",
        H("Pronko's Dyck-class operator commutes with the periodic Fredkin Hamiltonian"),
        Blocks(
            DefinitionNode("pathHeight", "Height of a spin-word path", PathHeightFormula(),
                "The letter 0 (spin up) is a step up and the letter 1 (spin down) is a step down; the height after i letters sums these steps over the sites t in Fin N with t below i."),
            DefinitionNode("inClass", "Membership in the Dyck class C_(a,b)(N)", InClassFormula(),
                "Started at height a, the path of the word stays at height at least zero, touches height zero at some index between 0 and N, and ends at height b, as in section 2.2."),
            DefinitionNode("Xi", "Pronko's operator Xi", XiFormula(),
                "The outer sum runs over k from 0 to the floor of N/2 with sign (-1)^k; the inner sum runs over the words of the class C_(k,k)(N), each contributing the product of the one-site spin-up and spin-down projections selected by its letters, as in equation (4.1)."),
            DefinitionNode("claim", "The commutation relation of section 4.1", ClaimDefinitionFormula(),
                "For every even number of sites N at least three, Xi commutes with the periodic Fredkin Hamiltonian H of equation (2.3)."),
            TheoremNode("result", "Xi commutes with the Hamiltonian", ClaimFormula(),
                "Xi is diagonal: its value at a word is (-1)^a when the word is balanced and lies in C_(a,a)(N), where a is the negative of the smallest height, and zero otherwise. The off-diagonal part of the density F_(j,j+1,j+2) exchanges the letters at j + 1 and j + 2 when the letter at j is up, or the letters at j and j + 1 when the letter at j + 2 is down, indices modulo N. Such an exchange keeps the number of up letters. When it does not wrap around the end of the word it changes a single height by two, and the control letter forces the smaller of the two values to occur at another index, so the smallest height and a are unchanged. When it exchanges the last and the first letter, every interior height moves by the same amount, and the control letter forces an interior height at most zero in both words, so a changes by zero or two. Hence a has the same parity at the two words, Xi commutes with every density, and so with their sum H. The argument uses only N at least three."))),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation"))]));

    private static DocumentBlock DefinitionNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pronko-xi-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static DocumentBlock TheoremNode(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("pronko-xi-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ComplexNumbers() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name)
    {
        var tokens = new List<Formula>();
        foreach (var part in name.Split('.'))
        {
            if (tokens.Count > 0) tokens.Add(Dot);
            tokens.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. tokens])));
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Below(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Negative(Formula value) => new Formula.Negate(Parenthesized(value));
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula n) => new Formula.TypeArrow(Fin(n), Fin(D(2)));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Height(Formula word, Formula index) => Call("pathHeight", word, index);

    private static Formula PathHeightFormula()
    {
        Formula n = F.Id("N"), l = F.Id("ell"), i = F.Id("i"), t = F.Id("t");
        Formula step = Call("ite", Equal(new Formula.Apply(l, [t]), D(0)), D(1), Negative(D(1)));
        Formula index = Seq(t, Sp, InMacro, Sp, Fin(n), Comma, Sp, Below(t, i));
        Formula sum = Seq(new Formula.Subscript(Sum, index), Sp, Parenthesized(step));
        return Disp(All("N", Naturals(), All("ell", Word(n), All("i", Naturals(),
            Equal(Height(l, i), sum)))));
    }

    private static Formula InClassBody(Formula n, Formula a, Formula b, Formula l)
    {
        Formula i = F.Id("i");
        Formula shifted = Add(a, Height(l, i));
        Formula stays = All("i", Naturals(), Implies(AtMost(i, n), AtMost(D(0), shifted)));
        Formula touches = Some("i", Naturals(), And(AtMost(i, n), Equal(shifted, D(0))));
        Formula ends = Equal(Add(a, Height(l, n)), b);
        return And(stays, And(touches, ends));
    }

    private static Formula InClassFormula()
    {
        Formula n = F.Id("N"), a = F.Id("a"), b = F.Id("b"), l = F.Id("ell");
        Formula body = new Formula.Logic(Call("inClass", n, a, b, l), FormulaLogicOperator.Iff,
            Parenthesized(InClassBody(n, a, b, l)));
        return Disp(All("N", Naturals(), All("a", Naturals(), All("b", Naturals(),
            All("ell", Word(n), body)))));
    }

    private static Formula XiFormula()
    {
        Formula n = F.Id("N"), k = F.Id("k"), l = F.Id("ell"), i = F.Id("i");
        Formula local = Call("ite", Equal(new Formula.Apply(l, [i]), D(0)), F.Id("nUp"), F.Id("nDown"));
        Formula projector = Call("tensor", n, Parenthesized(Seq(i, Sp, Mapsto, Sp, local)));
        Formula innerIndex = Seq(l, Colon, Sp, Call("inClass", n, k, k, l));
        Formula inner = Seq(new Formula.Subscript(Sum, innerIndex), Sp, Parenthesized(projector));
        Formula sign = new Formula.Power(Parenthesized(Negative(D(1))), k);
        Formula top = new Formula.Floor(new Formula.Fraction(n, D(2)));
        Formula outerIndex = Seq(k, Sp, InMacro, Sp, Call("Finset.range", Add(top, D(1))));
        Formula outer = Seq(new Formula.Subscript(Sum, outerIndex), Sp, Parenthesized(Multiply(sign, inner)));
        return Disp(All("N", Naturals(), Equal(Call("Xi", n), outer)));
    }

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N");
        Formula commute = Equal(Multiply(Call("Xi", n), Call("H", n)), Multiply(Call("H", n), Call("Xi", n)));
        return All("N", Naturals(), Implies(AtMost(D(3), n), Implies(Call("Even", n), commute)));
    }

    private static Formula ClaimDefinitionFormula() => Disp(
        new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));

    private static Formula ClaimFormula() => Disp(ClaimBody());
}

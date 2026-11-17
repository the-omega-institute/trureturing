using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class CyclicDifferencePrimeContentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/CyclicDifferencePrimeContent.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/andersonweippert2024controlled");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The content of every positive cyclic difference is a prime power.", H("Prime-power content of cyclic differences"), Blocks(
            Node("cyclic-coefficients", "Differences of a single occupied block", "coeff", CoeffFormula(),
                "The initial coefficient is one at residue one and zero elsewhere. Each next row is the cyclic difference of its predecessor.", DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("order-prime-power", "Annihilating coefficients force prime-power order", "order_prime_power_of_coeff", OrderFormula(),
                "For any group element, annihilation by every coefficient makes its order divide their gcd. A divisor of a power of p is itself a power of p.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static Formula V(string name) => F.Id(name);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula App(Formula head, params Formula[] args)
        {
            var items = new List<Formula>();
            for (var i = 0; i < args.Length; i += 1)
            {
                if (i > 0) { items.Add(Comma); items.Add(Sp); }
                items.Add(args[i]);
            }
            return Seq(head, Parenthesized(Seq([.. items])));
        }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Rightarrow, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Bracket(Formula type) => Seq(OpenBracket, type, CloseBracket);
    private static Formula Instance(Formula type, Formula body) => Seq(Bracket(type), Comma, Sp, body);
    private static Formula Zm(Formula p) => Call("ZMod", p);
    private static Formula PrimeCtx(Formula body) => All("p", N(), Instance(Call("NeZero", V("p")), body));
    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance) =>
            Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
                StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula CoeffFormula()
    {
        Formula p = V("p"), r = V("r"), j = V("j");
        Formula initial = PrimeCtx(All("j", Zm(p), Eqn(Call("coeff", p, D(0), j),
            Call("ite", Eqn(j, D(1)), D(1), D(0)))));
        Formula next = PrimeCtx(All("r", N(), All("j", Zm(p),
            Eqn(Call("coeff", p, Add(r, D(1)), j), Sub(Call("coeff", p, r, j), Call("coeff", p, r, Sub(j, D(1))))))));
        return Disp(new Formula.Aligned([initial, next]));
    }
    private static Formula OrderFormula()
    {
        Formula p = V("p"), r = V("r"), m = V("m"), g = V("g"), j = V("j"), group = V("G");
        Formula annihilation = All("j", Zm(p), Eqn(Pow(g, Call("coeff", p, Add(r, D(1)), j)), D(1)));
        Formula conclusion = Ex("m", N(), Eqn(Call("orderOf", g), Pow(p, m)));
        return Disp(All("G", V("Type"), Instance(Call("Group", group), PrimeCtx(
            Imp(App(Q("Nat", "Prime"), p), All("g", group,
                All("r", N(), Imp(annihilation, conclusion))))))));
    }
}

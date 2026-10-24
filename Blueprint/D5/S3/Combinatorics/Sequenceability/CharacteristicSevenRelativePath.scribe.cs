using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Sequenceability;

internal sealed class CharacteristicSevenRelativePathDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Sequenceability/CharacteristicSevenRelativePath.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula K => V("K");
    private static Formula FieldBind(Formula body) => All("K", Call("Type"),
        All("f", Call("Field", K), All("finite", Call("Finite", K), body)));

    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (int i = clauses.Length - 2; i >= 0; --i) result = And(clauses[i], result);
        return result;
    }
    private static Formula RelativePathFormula()
    {
        Formula u = V("u"), v = V("v"), w = V("w"), n = V("n");
        Formula G = Seq(Call("ZMod", D(7)), Sp, Times, Sp, K);
        Formula N = Add(Mul(D(6), Call("card", K)), D(1));
        Formula Vn(Formula x) => Apply(v, x);
        Formula Wn(Formula x) => Apply(w, x);
        Formula B = Seq(OpenBrace, V("z"), Colon, G, Mid, Ne(Call("fst", V("z")), D(0)), CloseBrace);
        Formula labels = Seq(B, Sp, Cup, Sp, OpenBrace, Pair(D(0), u), CloseBrace);
        Formula restrictedV = Call("restrict", v, Call("Fin", Add(N, D(1))));
        Formula restrictedW = Call("restrict", w, Call("Fin", N));
        Formula prefix(Formula x) => Call("sum", Call("range", x), w);
        Formula body = Ex("v", Call("Function", Call("Nat"), G),
            Ex("w", Call("Function", Call("Nat"), G), Conjoin(
                Eqn(Vn(D(0)), Pair(D(0), D(0))), Eqn(Vn(N), Pair(D(0), u)),
                Call("Injective", restrictedV),
                Eqn(Call("range", Call("interior", v, Sub(N, D(1)))), B),
                All("n", Call("Nat"), Imp(Call("lt", n, N), Eqn(Wn(n), Sub(Vn(Add(n, D(1))), Vn(n))))),
                Call("Injective", restrictedW), Eqn(Call("range", restrictedW), labels),
                Eqn(Call("length", Call("ofFn", restrictedV)), Add(N, D(1))),
                Eqn(Call("length", Call("ofFn", restrictedW)), N),
                Call("Nodup", Call("ofFn", restrictedV)), Call("Nodup", Call("ofFn", restrictedW)),
                All("n", Call("Nat"), Imp(Call("le", n, N), Eqn(prefix(n), Vn(n)))),
                Call("Injective", Call("boundedPrefixes", w, Add(N, D(1)))),
                All("a", Call("Nat"), All("b", Call("Nat"),
                    Imp(Call("lt", V("a"), V("b")), Imp(Call("le", V("b"), N),
                        Ne(Call("sum", Call("Ico", V("a"), V("b")), w), Pair(D(0), D(0))))))),
                Eqn(prefix(N), Pair(D(0), u)))));
        return Disp(FieldBind(All("char", Call("CharP", K, D(7)), All("u", K, Imp(Ne(u, D(0)), body)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked returns, complete relative paths and exact prefix sums over characteristic-seven fields.",
        H("Characteristic-seven complete relative path"), Blocks(
            Paragraph(Text("The affine lift, seam equations and vector-label conservation are supplied by "
                + "CharacteristicSevenDetour. The marked-return construction proves that the particular "
                + "overlapping surgery has one orbit on the entire carrier. Its bounded enumeration gives "
                + "the complete relative path, with no claim of literature novelty.")),
            Describe.Lean(DescribeId.Create("characteristic-seven-detour-relative-path"),
                DeclarationHandle.Create(Prefix + "exists_characteristic_seven_relative_path"),
                H("Complete relative path over every finite characteristic-seven field"),
                StatementSource.FromAuthor(RelativePathFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The carrier is (Fin(6) times K) plus two endpoints. The inverse base permutation "
                        + "has four distinct marked cycles represented by headOne, headTwo, target and source. "
                        + "The original FiniteEndpointPairing.first_visit_reattach and same_cycle_of_first_visit "
                        + "interfaces identify the repaired marked return; FiniteBandSwitch.same_cycle_perm_congr "
                        + "transports its explicit four-cycle. Every base inverse edge connects points of the repaired "
                        + "orbit, proving whole-carrier connectivity rather than only the endpoint closing edge.")),
                    Paragraph(Text("The label reindexing is swap(predecessorOne,source) times "
                        + "swap(predecessorTwo,source). It fixes target and permutes all other tails. "
                        + "Thus the two removed full vector labels are reassigned to predecessorTwo and source, "
                        + "while predecessorOne receives (0,u). Removing target deletes exactly (0,-u). "
                        + "The resulting label map is bijective onto the nonzero columns together with (0,u).")),
                    Paragraph(Text("N=6 card(K)+1. Restrict(v,Fin(N+1)) and restrict(w,Fin(N)) are the bounded "
                        + "vertex and label lists. Interior(v,N-1) means i maps to v(i+1) on Fin(N-1), and "
                        + "boundedPrefixes(w,N+1) includes both the empty and full prefix. The one-cycle "
                        + "enumeration starts at source and ends at target because Q(target)=source. "
                        + "Telescoping identifies every prefix with its vertex and every interval with the "
                        + "difference of two distinct vertices, including the full interval.")),
                    Paragraph(Text("No extension-degree or primitive-generator exception is assumed. "
                        + "The construction covers both primitive generators of F7. The arbitrary-subset, "
                        + "same-M and original-coordinate parent problem is outside this theorem."))), DescribeRole.Theorem))));
}

using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class BinaryBinBaseChangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary bins over a characteristic-zero field carry the scalar-extended one-bin and two-bin sl₂ actions.",
        H("Scalar extension and two binary bins"),
        Blocks(
            Paragraph(Text("Let K be a field of characteristic zero. A bin of length m is indexed by the Boolean words Fin(m) → Bool. Its vector space consists of K-valued functions on these words. The function δ(w) is Pi.single(w,1), equal to one at w and zero elsewhere. Rational weights and operator coefficients are interpreted in K through the unique rational algebra map. Products of endomorphisms mean composition. Tensor products in the two-bin formulas are over K; the tensor product used for scalar extension is over the rationals.")),
            Node("extend", "Extension in delta coordinates", Extension(), true,
                "The equivalence piScalarRight sends z tensor φ to the function u ↦ φ(u)z. Conjugating baseChange by this equivalence gives an endomorphism in finite function coordinates. It sends each delta function to the rational image with every coefficient interpreted in K."),
            Node("binWeight", "Extended weight multiplication", BinDefinition("binWeight", "weight"), true,
                "The rational diagonal weight operator is extended to K. On a delta function at w it multiplies by the rational weight of w interpreted in K."),
            Node("binRaising", "Extended raising", BinDefinition("binRaising", "Rbin"), true,
                "The rational raising operator has coefficient (p+1)(m−p−1) on each permitted adjacent swap. Scalar extension preserves these coefficients in K."),
            Node("binLowering", "Extended lowering", BinDefinition("binLowering", "Hbin"), true,
                "The rational lowering operator sums the permitted adjacent swaps with coefficient one. Its scalar extension has the same delta coefficients in K."),
            Node("bin_action", "One-bin relations and delta coefficients", BinAction(), false,
                "The one-bin triple supplies the relations for m at least two. At lengths zero and one there are no inner bonds and every weight is zero, so the action is zero. The delta identification applies to each of the three operators."),
            Node("twoWeight", "Two-bin weight", TwoDefinition("twoWeight", "binWeight"), true,
                "The weight operator is the sum of the first-factor and second-factor weight operators."),
            Node("twoRaising", "Two-bin raising", TwoDefinition("twoRaising", "binRaising"), true,
                "Raising acts in either bin, leaving the other factor fixed."),
            Node("twoLowering", "Two-bin lowering", TwoDefinition("twoLowering", "binLowering"), true,
                "Lowering acts in either bin, leaving the other factor fixed."),
            Node("two_bin_action", "Two-bin relations and delta tensors", TwoAction(), false,
                "Operators on different tensor factors commute. Expanding each commutator therefore leaves the sum of the two one-bin commutators. Delta tensors have total weight equal to the sum of the two bin weights; raising and lowering replace either delta factor by its coefficientwise extended image.")),
        []));

    private static DocumentBlock.Describe Node(string name, string title, Formula formula,
        bool definition, string prose) =>
        Describe.Lean(DescribeId.Create("binary-bin-base-change-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/SpinChains/BinaryBinBaseChange." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), definition ? DescribeRole.Definition : DescribeRole.Theorem);

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Parenthesized(x), FormulaLogicOperator.And, Parenthesized(y));
    private static Formula PlusOf(Formula x, Formula y) => Seq(x, Sp, Plus, Sp, y);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Smul(Formula x, Formula y) => Seq(x, Sp, Cdot, Sp, y);
    private static Formula Tensor(Formula x, Formula y) =>
        Call("tensor", x, y);
    private static Formula ArrowOf(Formula x, Formula y) => new Formula.TypeArrow(x, y);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula Assumption(Formula x, Formula body) =>
        Seq(OpenBracket, x, CloseBracket, Sp, body);
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rats => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Scalar => F.Id("K");
    private static Formula Words(Formula m) => ArrowOf(Call("Fin", m), Call("Bool"));
    private static Formula Space(Formula m) => ArrowOf(Words(m), Scalar);
    private static Formula Delta(Formula w) => Call("PiSingle", w, D(1));
    private static Formula Weight(Formula w) => Call("weight", w);
    private static Formula Cast(Formula x) => Parenthesized(Seq(x, Sp, Colon, Sp, Scalar));
    private static Formula Op(string name, Formula m) => Call(name, Scalar, m);
    private static Formula Two(string name) => Call(name, Scalar, F.Id("m"), F.Id("n"));
    private static Formula Relations(Formula h, Formula e, Formula f) => new Formula.Apply(
        Seq(Operatorname, Grp(F.Id("Sl"), D(2), F.Id("Relations"))), [h, e, f]);
    private static Formula End(Formula scalar, Formula space) => Call("End", scalar, space);

    private static Formula Environment(Formula body, bool charZero = true) => All("K", Call("Type"),
        Assumption(Call("Field", Scalar), charZero ? Assumption(Call("CharZero", Scalar), body) : body));
    private static Formula Bins(Formula body, bool two, bool charZero = true) => Environment(All("m", Nats,
        two ? All("n", Nats, body) : body), charZero);

    private static Formula Extension()
    {
        var i = F.Id("I"); var a = F.Id("A");
        var right = At(Call("conjRingEquiv", Call("piScalarRight", Rats, Scalar, Scalar, i)),
            At(Call("baseChangeHom", Rats, Scalar, ArrowOf(i, Rats)), a));
        return Environment(All("I", Call("Type"),
            Assumption(Call("Fintype", i), Assumption(Call("DecidableEq", i),
                All("A", End(Rats, ArrowOf(i, Rats)), Eq(Call("extend", Scalar, a), right))))));
    }

    private static Formula BinDefinition(string name, string source)
    {
        var m = F.Id("m"); var w = F.Id("w");
        var expression = source == "weight"
            ? Call("mulLeft", Scalar, Lambda("w", Words(m), Cast(Weight(w))))
            : Call("extend", Scalar, Call(source, m));
        return Bins(Eq(Op(name, m), expression), false, source != "weight");
    }

    private static Formula TwoDefinition(string name, string source)
    {
        var m = F.Id("m"); var n = F.Id("n");
        return Bins(Eq(Two(name), PlusOf(
            Call("rTensor", Op(source, m), Space(n)),
            Call("lTensor", Op(source, n), Space(m)))), true, source != "binWeight");
    }

    private static Formula RationalImage(string source, Formula m, Formula w, Formula u) =>
        At(At(Call(source, m), Delta(w)), u);

    private static Formula BinAction()
    {
        var m = F.Id("m"); var w = F.Id("w"); var u = F.Id("u");
        Formula coefficients = And(
            Eq(At(At(Op("binWeight", m), Delta(w)), u), Mul(Cast(Weight(u)), At(Delta(w), u))),
            And(Eq(At(At(Op("binRaising", m), Delta(w)), u), Cast(RationalImage("Rbin", m, w, u))),
                Eq(At(At(Op("binLowering", m), Delta(w)), u), Cast(RationalImage("Hbin", m, w, u)))));
        return Bins(And(Relations(Op("binWeight", m), Op("binRaising", m), Op("binLowering", m)),
            All("w", Words(m), All("u", Words(m), coefficients))), false);
    }

    private static Formula Image(string source, Formula m, Formula w) =>
        Lambda("u", Words(m), Cast(RationalImage(source, m, w, F.Id("u"))));

    private static Formula TwoAction()
    {
        var m = F.Id("m"); var n = F.Id("n"); var w = F.Id("w"); var v = F.Id("v");
        var delta = Tensor(Delta(w), Delta(v));
        Formula move(string op, string source) => Eq(At(Two(op), delta), PlusOf(
            Tensor(Image(source, m, w), Delta(v)), Tensor(Delta(w), Image(source, n, v))));
        Formula coefficients = And(Eq(At(Two("twoWeight"), delta),
            Smul(Parenthesized(PlusOf(Cast(Weight(w)), Cast(Weight(v)))), delta)),
            And(move("twoRaising", "Rbin"), move("twoLowering", "Hbin")));
        return Bins(And(Relations(Two("twoWeight"), Two("twoRaising"), Two("twoLowering")),
            All("w", Words(m), All("v", Words(n), coefficients))), true);
    }
}

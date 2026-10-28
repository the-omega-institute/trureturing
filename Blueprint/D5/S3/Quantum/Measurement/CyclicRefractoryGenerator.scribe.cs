using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class CyclicRefractoryGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite quantum instrument reproduces every word of a residue-labelled refractory process.",
        H("Cyclic Refractory Quantum Generator"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-refractory-generator"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Measurement/CyclicRefractoryGenerator.cyclic_refractory_generator"),
            H("A completely positive channel with the exact classical word law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The residue set is finite and decidable. The real amplitudes at each residue "
                    + "have squared sum one. The residue update is an arbitrary permutation; "
                    + "it need not consist of a single cycle. The Hilbert basis is indexed by "
                    + "a two-valued block coordinate and a residue.")),
                Paragraph(Text(
                    "In each block the free vector is (1,0), and the tail vector has coordinates "
                    + "(a(z),b(z)). The zero operator has rows (a(z),b(z)) and (0,0). "
                    + "The one operator in block z is the outer product of the tail vector "
                    + "at e(z) and the row (b(z),-a(z)); its output is shifted to residue e(z). "
                    + "These explicit operators are Kzero and Kone. The Boolean branchK chooses "
                    + "Kone for true and Kzero for false.")),
                Paragraph(Text(
                    "The zero branch maps the free vector to a(z) times that vector and maps "
                    + "the tail vector to the free vector. The one branch maps the free vector "
                    + "to b(z) times the next residue's tail vector and annihilates the tail vector. "
                    + "The corresponding classical weights are "
                    + "1-p(z), p(z), 1 and 0, with p(z)=b(z) squared.")),
                Paragraph(Text(
                    "The stateVec function selects the free vector for block coordinate zero "
                    + "and the tail vector for block coordinate one. The wordK recursion uses "
                    + "identity for the empty word and multiplies the remaining word operator "
                    + "on the left of its first branch. The independently defined "
                    + "classicalWordProbability recursion multiplies the first transition weight "
                    + "by the probability of the remaining word from the updated classical state.")),
                Paragraph(Text(
                    "The channel is completely positive at every matrix amplification and "
                    + "preserves trace. In the formula, matrix converts its CStarMatrix output "
                    + "back to an ordinary matrix, ofMatrix converts its input, and star on "
                    + "vectors is entrywise conjugation. "
                    + "The word equality includes the empty word, impossible words and "
                    + "zero transition weights.")),
                Paragraph(Text(
                    "The proof first computes each one-step vector update. Induction on the "
                    + "word then gives the product of transition amplitudes and the final "
                    + "state vector. A second induction identifies its squared amplitude with "
                    + "the classical recursive probability. Unit vector normalization converts "
                    + "this identity to a branch trace. The existing finite Kraus channel "
                    + "construction supplies complete positivity and trace preservation.")),
                Paragraph(Text(
                    "Quantum simulation of stochastic processes is an established subject. "
                    + "This theorem gives an explicit finite refractory family. It does not "
                    + "establish a minimum memory dimension, an entropy advantage, a stationary "
                    + "initial law or a physical implementation."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        arguments.Length == 0 ? Seq(Operatorname, Grp(F.Id(name))) :
            Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula TheoremFormula()
    {
        Formula zType = F.Id("Z"), a = F.Id("a"), b = F.Id("b"), e = F.Id("e");
        Formula z = F.Id("z"), s = F.Id("s"), w = F.Id("w"), x = F.Id("x");
        Formula c = F.Id("C"), rho = Rho;
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula carrier = Seq(Call("Fin", Num(2)), Sp, Times, Sp, zType);
        Formula matrix = Call("Matrix", carrier, carrier, complex);
        Formula k = Call("branchK", a, b, e, x);
        Formula kw = Call("wordK", a, b, e, w);
        Formula v = Call("stateVec", a, b, s);
        Formula normalized = Seq(Forall, Sp, z, Colon, Sp, zType, Comma, Sp,
            new Formula.Power(Apply(a, z), Num(2)), Sp, Plus, Sp,
            new Formula.Power(Apply(b, z), Num(2)),
            Sp, Eq, Sp, Num(1));
        Formula channelAction = Seq(
            Forall, Sp, rho, Colon, Sp, matrix, Comma, Sp,
            Equal(Call("matrix", Apply(c, Call("ofMatrix", rho))),
                Seq(Sum, Underscore, Grp(x, Sp, InMacro, Sp, Call("Bool")), Sp,
                    Mul(Mul(k, rho), Call("adjoint", k)))));
        Formula words = Seq(
            Forall, Sp, s, Colon, Sp, carrier, Comma, Sp,
            w, Colon, Sp, Call("List", Call("Bool")), Comma, RowBreak, Grp(),
            Equal(
                Call("Tr", Mul(Mul(kw, Call("vecMulVec", v, Call("star", v))),
                    Call("adjoint", kw))),
                Call("complex", Call("classicalWordProbability",
                    Seq(Open, z, Sp, Mapsto, Sp,
                        new Formula.Power(Apply(b, z), Num(2)), Close),
                    e, s, w))));
        return Disp(Seq(
            Forall, Sp, zType, Colon, Sp, Call("Type"), Comma, Sp,
            Call("Fintype", zType), Comma, Sp, Call("DecidableEq", zType), Comma,
            RowBreak, Grp(),
            a, Comma, Sp, b, Colon, Sp, zType, Sp, To, Sp, real, Comma, Sp,
            e, Colon, Sp, Call("Perm", zType), Comma, RowBreak, Grp(),
            Open, normalized, Close, Sp, Implies, RowBreak, Grp(),
            Exists, Sp, c, Colon, Sp, Call("QuantumChannel", carrier, carrier), Comma,
            RowBreak, Grp(), Open, channelAction, Close, Sp, Land, RowBreak, Grp(),
            words, Dot));
    }
}

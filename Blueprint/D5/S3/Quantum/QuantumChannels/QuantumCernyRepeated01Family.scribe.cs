using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class QuantumCernyRepeated01FamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/QuantumCernyRepeated01Family.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/lee2026quantumcerny");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every binary word of the form 01 u 01 z 1, with arbitrary binary words u and z, a dimension-three rank obstruction prevents it from being the unique shortest synchronizing word of two qubit channels.",
        H("A repeated 01 family of qubit synchronization obstructions"),
        Blocks(
            Node("word", "Repeated 01 words", RepeatedFormula(),
                "The two intervening words are arbitrary binary lists; the final 1 is fixed.",
                "repeated01", DescribeRole.Definition),
            Node("rank", "A dimension-three rank obstruction", RepeatedLemmaFormula(),
                "If the family word has zero composite map, one of four structural words has zero composite map. Each is strictly shorter, independently of the two intervening lengths.",
                "mortal_repeated01", DescribeRole.Theorem),
            Node("channel", "No unique shortest qubit instance", RepeatedChannelFormula(),
                "Differences of reachable qubit states span an invariant space of dimension at most three. Restriction turns synchronization into zero action on that space, and the rank obstruction supplies a different shorter synchronizing word.",
                "no_qubit_instance_repeated01", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role) => Describe.Lean(
            DescribeId.Create("qcerny-family-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Or, Par(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Words() => Call("List", Fin(D(2)));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Bits(params byte[] values)
    {
        var parts = new System.Collections.Generic.List<Formula> { OpenBracket };
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) { parts.Add(Comma); parts.Add(Sp); }
            parts.Add(D(values[i]));
        }
        parts.Add(CloseBracket);
        return Seq([.. parts]);
    }
    private static Formula Append(Formula a, Formula b) =>
        App(Seq(Named("List"), Dot, Named("append")), a, b);

    private static Formula RepeatedFormula()
    {
        Formula u = F.Id("u"), z = F.Id("z"), pair = Bits(0, 1);
        Formula word = Append(Append(Append(Append(pair, u), pair), z), Bits(1));
        return Disp(All(u, Words(), All(z, Words(), Eq(Call("repeated01", u, z), word))));
    }

    private static Formula RepeatedLemmaFormula()
    {
        Formula k = F.Id("K"), v = F.Id("V"), f = F.Id("f"), u = F.Id("u"), z = F.Id("z");
        Formula pair = Bits(0, 1), one = Bits(1);
        Formula zero(Formula word) => Eq(Call("wordComp", f, word), D(0));
        Formula prefix = Append(Append(pair, u), pair);
        Formula tail = Append(Append(pair, z), one);
        Formula dropFirst = Append(Append(Append(Append(one, u), pair), z), one);
        Formula dropLast = Append(Append(Append(pair, u), pair), z);
        Formula conclusion = Or(Or(zero(prefix), zero(tail)), Or(zero(dropFirst), zero(dropLast)));
        Formula hypotheses = And(Le(Call("finrank", k, v), D(3)), zero(Call("repeated01", u, z)));
        Formula structure = And(And(And(Call("Field", k), Call("AddCommGroup", v)),
            Call("Module", k, v)), Call("FiniteDimensional", k, v));
        return Disp(All(Seq(k, Comma, Sp, v), Call("Type"), Imp(structure,
            All(f, Arrow(Fin(D(2)), Call("End", k, v)),
                All(u, Words(), All(z, Words(), Imp(hypotheses, conclusion)))))));
    }

    private static Formula RepeatedChannelFormula()
    {
        Formula u = F.Id("u"), z = F.Id("z");
        return Disp(All(u, Words(), All(z, Words(),
            new Formula.Not(Call("HasInstance", D(2), Call("repeated01", u, z))))));
    }
}

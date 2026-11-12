using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class PauliFrameTraceTableDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Tomography/PauliFrameTraceTable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two labelled Pauli frames have the same finite trace table, with a non-real complex-frame witness.",
        H("Pauli frame trace table"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frame"),
                DeclarationHandle.Create(Module + ".frame"),
                H("The labelled Pauli frame projectors"),
                StatementSource.FromAuthor(Disp(FrameFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Boolean label selects the real third context G^r or the complex third context G^c. "
                        + "The first two contexts are the fixed E and F Pauli pairs, and each context is indexed "
                        + "by the two signs in Fin 2 × Fin 2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-table"),
                DeclarationHandle.Create(Module + ".trace_table"),
                H("Both frames have the same twelve-entry trace table"),
                StatementSource.FromAuthor(Disp(TraceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For either choice of the third context, equal context labels give the Kronecker delta "
                        + "on the two sign pairs, while distinct contexts have trace overlap 1/4. "
                        + "The proof expands the four Pauli terms and applies the frozen two-qubit Pauli trace "
                        + "orthogonality theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-frame-nonreal-witness"),
                DeclarationHandle.Create(Module + ".complex_frame_nonreal_witness"),
                H("The complex frame has a non-real matrix entry"),
                StatementSource.FromAuthor(Disp(WitnessFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Y ⊗ I Pauli word has an explicitly computed entry with nonzero imaginary part. "
                        + "This is a finite separation witness for the complex frame; the full Jordan-closure "
                        + "dimension claims remain outside this module."))),
                DescribeRole.Theorem))));

    private static Formula TraceFormula()
    {
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula st = F.Id("st");
        Formula uv = F.Id("uv");
        Formula fin2 = Call("Fin", D(2));
        Formula bits = Call("Prod", fin2, fin2);
        Formula fin3 = Call("Fin", D(3));
        Formula lhs = Call("trace", Call("mul", Call("frame", c, i, st), Call("frame", c, j, uv)));
        Formula rhs = Call("if", Call("Eq", i, j),
            Call("if", Call("Eq", st, uv), D(1), D(0)),
            new Formula.Fraction(D(1), D(4)));
        return All("c", F.Id("Bool"),
            All("i", fin3,
                All("j", fin3,
                    All("st", bits,
                        All("uv", bits, new Formula.Relation(lhs, FormulaRelationOperator.Equal, rhs))))));
    }

    private static Formula FrameFormula()
    {
        Formula c = F.Id("c");
        Formula i = F.Id("i");
        Formula st = F.Id("st");
        Formula fin2 = Call("Fin", D(2));
        Formula bits = Call("Prod", fin2, fin2);
        Formula fin3 = Call("Fin", D(3));
        Formula matrix = Call("Matrix", Arrow(fin2, fin2), Arrow(fin2, fin2), F.Id("Complex"));
        Formula body = Call("frame", c, i, st);
        Formula rhs = Call("if", Call("Eq", i, D(0)), Call("E", st),
            Call("if", Call("Eq", i, D(1)), Call("F", st),
                Call("if", c, Call("Gr", st), Call("Gc", st))));
        return All("c", F.Id("Bool"),
            All("i", fin3,
                All("st", bits,
                    new Formula.Relation(body, FormulaRelationOperator.Equal,
                        rhs))));
    }

    private static Formula WitnessFormula()
    {
        Formula fin2 = Call("Fin", D(2));
        Formula index = Arrow(fin2, fin2);
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula word = Call("wordOp", Call("yI"));
        Formula entry = Call("im", Call("apply", Call("apply", word, x), y));
        return Exists("x", index, Exists("y", index,
            new Formula.Relation(entry, FormulaRelationOperator.NotEqual, D(0))));
    }

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));

    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] args)
    {
        Formula function = Seq(Operatorname, Grp(F.Id(name)));
        var content = new List<Formula> { function, Open };
        for (var index = 0; index < args.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(args[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
}

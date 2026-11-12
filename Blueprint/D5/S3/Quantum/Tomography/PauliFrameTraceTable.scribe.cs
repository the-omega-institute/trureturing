using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class PauliFrameTraceTableDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Tomography/PauliFrameTraceTable";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same labelled Pauli overlap table has generated real Jordan carriers of dimensions ten and sixteen.",
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
                H("Both triples have the same twelve-by-twelve trace table"),
                StatementSource.FromAuthor(Disp(TraceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For either choice of the third context, equal context labels give the Kronecker delta "
                        + "on the two sign pairs, while distinct contexts have trace overlap 1/4. "
                        + "The proof expands the four Pauli terms and applies the frozen two-qubit Pauli trace "
                        + "orthogonality theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("real-generated"),
                DeclarationHandle.Create(Module + ".real_generated"),
                H("The real triple generates all real symmetric matrices"),
                StatementSource.FromAuthor(Disp(Call("Eq", Call("generated", Call("frame", F.Id("true"))), F.Id("realCarrier")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier is the intersection of all real subspaces containing all twelve original "
                        + "projectors and closed under the matrix Jordan product. Signed sums recover XI, IX, ZI, "
                        + "and IZ. Their Jordan products supply XZ and ZX, whose product supplies YY. These ten "
                        + "Pauli words span every real symmetric matrix, and the original real projectors lie in "
                        + "that Jordan-closed carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-generated"),
                DeclarationHandle.Create(Module + ".complex_generated"),
                H("The complex triple generates all Hermitian matrices"),
                StatementSource.FromAuthor(Disp(Call("Eq", Call("generated", Call("frame", F.Id("false"))), F.Id("complexCarrier")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed sums of G^c additionally supply YI and IY. Multiplying commuting operators "
                        + "on the two tensor factors gives every two-qubit Pauli word. Pauli expansion with real "
                        + "coefficients then supplies every Hermitian matrix in the original common environment."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("generated-dimensions"),
                DeclarationHandle.Create(Module + ".generated_dimensions"),
                H("The generated carriers have different real dimensions"),
                StatementSource.FromAuthor(Disp(Call("And",
                    Call("Eq", Call("finrank", F.Id("Real"), Call("generated", Call("frame", F.Id("true")))), D(1, 0)),
                    Call("Eq", Call("finrank", F.Id("Real"), Call("generated", Call("frame", F.Id("false")))), D(1, 6))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real carrier has one coordinate for each of the ten Pauli words containing an even "
                        + "number of Y factors. The full complex Hermitian carrier has real dimension sixteen."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("frame-complete"),
                DeclarationHandle.Create(Module + ".frame_complete"),
                H("Every context is a complete rank-one projector frame"),
                StatementSource.FromAuthor(Disp(All("c", F.Id("Bool"), Call("Complete", Call("frame", F.Id("c")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each context consists of four Hermitian rank-one idempotents. Distinct sign pairs give "
                        + "orthogonal projectors and their sum is the identity. The rank follows from the trace "
                        + "of the corresponding idempotent linear operator."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Whole-table determination of Jordan dimension"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proposed postprocessor is any function from the entire labelled twelve-by-twelve "
                        + "complex overlap table to a natural number. It must recover the real dimension of the "
                        + "smallest Jordan-closed real carrier for every complete triple in the fixed H4(C) environment."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("No whole-table postprocessor recovers Jordan dimension"),
                StatementSource.FromAuthor(Disp(Call("Not", F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two original complete triples have the same whole labelled trace table, while their "
                        + "generated real carriers have dimensions ten and sixteen. Any function of that table "
                        + "would have to assign both values to one input. This compares two frame witnesses in "
                        + "the same Hermitian algebra; it makes no assertion about two complete physical models."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        Formula fin3 = Call("Fin", D(3));
        Formula fin2 = Call("Fin", D(2));
        Formula bits = Call("Prod", fin2, fin2);
        Formula triples = Arrow(fin3, Arrow(bits, F.Id("Op")));
        Formula tables = Arrow(fin3, Arrow(fin3, Arrow(bits, Arrow(bits, F.Id("Complex")))));
        Formula conclusion = Call("Eq", Call("post", Call("table", F.Id("p"))),
            Call("finrank", F.Id("Real"), Call("generated", F.Id("p"))));
        return Exists("post", Arrow(tables, F.Id("Nat")),
            All("p", triples, Call("Implies", Call("Complete", F.Id("p")), conclusion)));
    }

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

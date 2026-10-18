using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers.BipartiteBlockade;

internal sealed class PhysicalSingleSettingLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual density-state ambiguities for one drive on every connected bipartite graph with two nonlinear neighborhoods.",
        H("The physical one-setting lower bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("physical-single-setting-lower"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/PhysicalSingleSettingLower.physical_single_setting_lower"),
            H("Coherent edge flow realizes indistinguishable physical states"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let G be a finite connected simple graph with a proper Boolean coloring. "
                    + "The drive at every vertex is nonzero; this includes every positive drive. "
                    + "Choose two vertices u and w with distinct open neighborhoods, each of "
                    + "cardinality at least two. All matrix indices are actual independent "
                    + "configurations of G. Occupation, blockade, the legal-flip Hamiltonian, "
                    + "and its double commutator are the source operators, rather than free "
                    + "readout variables.")),
                Paragraph(Text(
                    "The diagonal residual theorem supplies a signed diagonal direction with "
                    + "zero trace and all occupation moments zero. Its blockade vector is "
                    + "nonzero and obeys the one bipartite compatibility equation: the signed "
                    + "sum of squared drives times blockade moments is zero. Connectivity "
                    + "makes that compatibility equation sufficient for an edge flow.")),
                Paragraph(Text(
                    "For each edge, the proof adds a real Hermitian coherence between the "
                    + "two corresponding singleton configurations. Its coefficient is the "
                    + "edge flow divided by the product of endpoint drives. These terms "
                    + "leave every diagonal observable unchanged. The general double "
                    + "commutator identity shows that their acceleration contributions "
                    + "cancel those of the diagonal direction at every vertex.")),
                Paragraph(Text(
                    "The resulting Hermitian trace-zero matrix has zero occupation and "
                    + "double-commutator trace pairings and a nonzero real blockade pairing. "
                    + "The C-star norm bound for a self-adjoint matrix gives an explicit "
                    + "positive interval of perturbation sizes about the maximally mixed "
                    + "state. Both opposite perturbations are positive definite and trace "
                    + "one, and their difference is twice the perturbation size times the "
                    + "constructed matrix. Consequently the actual one-setting data "
                    + "coincide while at least one blockade expectation differs.")),
                Paragraph(Text(
                    "The theorem establishes the one-setting obstruction whenever two "
                    + "distinct nonlinear neighborhoods exist. It does not itself identify "
                    + "the exact affine dimension of the physical fiber, a uniform size "
                    + "of a positive-definite neighborhood, or recovery from higher time "
                    + "derivatives. Its equality of complex trace pairings is stronger "
                    + "than equality of the real occupation means and negative real "
                    + "double-commutator accelerations used in the data contract."))),
            DescribeRole.Theorem)),
        Blocks(Describe.Lean(
            DescribeId.Create("physical-zero-setting-lower"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/BipartiteBlockade/PhysicalSingleSettingLower.physical_zero_setting_lower"),
            H("A nonlinear neighborhood needs an acceleration setting"),
            StatementSource.FromAuthor(ZeroStatement()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Choose two distinct neighbors u and w of a center v with at least two "
                + "neighbors. Proper bipartite coloring makes u and w nonadjacent, so the "
                + "vacuum, each singleton, and the joint endpoint configuration are legal. "
                + "The equal mixture of vacuum and the joint configuration and the equal "
                + "mixture of the two singletons are positive semidefinite trace-one "
                + "matrices. Every occupation agrees, while the center's blockade "
                + "expectation is one half in the first state and zero in the second. "
                + "The construction requires neither connectivity nor a drive."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula C(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula Trace(Formula state, Formula effect) => C("trace", Seq(state, effect));
    private static Formula Eq(Formula left, Formula right) => Seq(left, Sp, F.Eq, Sp, right);
    private static Formula Conj(params Formula[] parts)
    {
        var items = new List<Formula>();
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(parts[i]);
        }
        return Seq([.. items]);
    }
    private static Formula ForV(Formula body) => Seq(Open, Forall, Sp, V("v"), Colon,
        V("V"), Comma, Sp, body, Close);
    private static Formula Statement()
    {
        var g = V("G"); var c = V("c"); var o = V("Ω");
        var r = V("ρ"); var s = V("σ"); var v = V("v");
        var n = C("number", g, v); var b = C("blockade", g, v);
        var h = C("hamiltonian", g, o);
        var d = C("commutator", h, C("commutator", h, n));
        var matrix = C("Matrix", C("Configuration", g), C("Configuration", g), C("Complex"));
        var assumptions = Conj(C("Connected", g), C("ProperColoring", g, c),
            ForV(Seq(C("Ω", v), Sp, Neq, Sp, D(0))),
            Seq(D(2), Sp, Le, Sp, C("card", C("neighborFinset", g, V("u")))),
            Seq(D(2), Sp, Le, Sp, C("card", C("neighborFinset", g, V("w")))),
            Seq(C("neighborFinset", g, V("u")), Sp, Neq, Sp,
                C("neighborFinset", g, V("w"))));
        var conclusion = Conj(C("PosSemidef", r), Eq(C("trace", r), D(1)),
            C("PosSemidef", s), Eq(C("trace", s), D(1)),
            ForV(Eq(Trace(r,n), Trace(s,n))), ForV(Eq(Trace(r,d), Trace(s,d))),
            Seq(Open, Exists, Sp, v, Colon, V("V"), Comma, Sp,
                C("re", Trace(r,b)), Sp, Neq, Sp, C("re", Trace(s,b)), Close));
        return Disp(Seq(Forall, Sp, V("V"), Colon, C("Type"), Comma, Sp,
            OpenBracket, C("Fintype", V("V")), CloseBracket, Comma, Sp,
            OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
            g, Colon, C("SimpleGraph", V("V")), Comma, Sp,
            c, Colon, Seq(V("V"), To, C("Bool")), Comma, Sp,
            o, Colon, Seq(V("V"), To, C("Real")), Comma, Sp,
            V("u"), Comma, V("w"), Colon, V("V"), Comma, Sp,
            assumptions, Rightarrow, Sp, Exists, Sp, r, Comma, s, Colon, matrix,
            Comma, Sp, conclusion, Dot));
    }

    private static Formula ZeroStatement()
    {
        var g = V("G"); var c = V("c"); var v = V("v");
        var r = V("ρ"); var s = V("σ");
        var matrix = C("Matrix", C("Configuration", g), C("Configuration", g), C("Complex"));
        var assumptions = Conj(C("ProperColoring", g, c),
            Seq(D(2), Sp, Le, Sp, C("card", C("neighborFinset", g, v))));
        var conclusion = Conj(C("PosSemidef", r), Eq(C("trace", r), D(1)),
            C("PosSemidef", s), Eq(C("trace", s), D(1)),
            Seq(Open, Forall, Sp, V("x"), Colon, V("V"), Comma, Sp,
                C("occupationMean", g,r,V("x")), Sp, F.Eq, Sp,
                C("occupationMean", g,s,V("x")), Close),
            Seq(C("blockadeMean",g,r,v), Sp, Neq, Sp, C("blockadeMean",g,s,v)));
        return Disp(Seq(Forall, Sp, V("V"), Colon, C("Type"), Comma, Sp,
            OpenBracket, C("Fintype", V("V")), CloseBracket, Comma, Sp,
            OpenBracket, C("DecidableEq", V("V")), CloseBracket, Comma, Sp,
            g, Colon, C("SimpleGraph", V("V")), Comma, Sp,
            c, Colon, Seq(V("V"), To, C("Bool")), Comma, Sp,
            v, Colon, V("V"), Comma, Sp, assumptions, Rightarrow, Sp,
            Exists, Sp, r, Comma, s, Colon, matrix, Comma, Sp, conclusion, Dot));
    }
}

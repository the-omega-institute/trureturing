using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class ToralReturnModuleStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/Dynamics/ToralReturnModuleStructure.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit residue maps classify the actual one-step integer return quotients and recover a group distinction invisible to every scalar return size.",
        H("Structure of the actual return groups"),
        Blocks(
            Paragraph(Text("Use the same C_k,D_k and actual quotient R(A,n) from ToralReturnModuleSpectrum. "
                + "All group structures below are induced by lattice addition. "
                + "The explicit classification also covers k=0 with ZMod(0)=Z.")),
            Describe.Lean(DescribeId.Create("actual-return-module-classification"),
                DeclarationHandle.Create(Prefix + "one_step_return_module_classification"),
                H("Two actual first-isomorphism constructions"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Call("Nonempty", Call("LinearEquiv", Call("Integer"), R("C", D(1)),
                        Call("ZMod", Call("mul", D(4), F.Id("k"))))), Sp, Land, Sp,
                    Call("Nonempty", Call("LinearEquiv", Call("Integer"), R("D", D(1)),
                        Call("Prod", Call("ZMod", D(2)), Call("ZMod", Call("mul", D(2), F.Id("k"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The maps on Z^2 are pi_C(x,y)=y mod 4k and "
                    + "pi_D(x,y)=(x mod 2,y-kx mod 2k). Each is surjective. "
                    + "The kernel of pi_C is exactly the image of C_k-I: from y=4ka take "
                    + "preimage (a,x-4ka). For pi_D, write x=2a and y-kx=2kb; "
                    + "the preimage under D_k-I is (b,a-kb). "
                    + "The Lean proof applies quotKerEquivOfSurjective after these literal image-kernel equalities."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("balanced-return-annihilator"),
                DeclarationHandle.Create(Prefix + "balanced_return_annihilated"),
                H("A uniform annihilator on the second quotient"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    Forall, Sp, F.Id("z"), Colon, Sp, R("D", D(1)), Comma, Sp,
                    Call("nsmul", Call("mul", D(2), F.Id("k")), F.Id("z")), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport to ZMod(2) times ZMod(2k). Multiplication by 2k "
                    + "vanishes in both coordinates, including the degenerate k=0 case. "
                    + "Injectivity of the constructed equivalence transports the equality back to the actual quotient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("companion-return-annihilator-witness"),
                DeclarationHandle.Create(Prefix + "companion_return_not_annihilated"),
                H("The first quotient retains a strictly stronger torsion order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("k"), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("z"), Colon, Sp, R("C", D(1)), Comma, Sp,
                    Call("NotEqual", Call("nsmul", Call("mul", D(2), F.Id("k")), F.Id("z")), D(0))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lift the residue one through the constructed cyclic equivalence. "
                    + "If 2k annihilated this element, 4k would divide 2k. Positivity of k excludes that divisibility. "
                    + "The witness is an element of the original quotient, not a separately supplied cyclic group."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("scalar-spectrum-structural-separation"),
                DeclarationHandle.Create(Prefix + "scalar_spectrum_and_structural_separation"),
                H("One-step group structure distinguishes equal all-time sizes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("k"), Colon, Sp, Call("Nat"), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("k"), Sp, Rightarrow, Sp,
                    Open, Forall, Sp, F.Id("n"), Colon, Sp, Call("Nat"), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("n"), Sp, Rightarrow, Sp,
                    Call("Nat.card", R("C", F.Id("n"))), Sp, Eq, Sp,
                    Call("Nat.card", R("D", F.Id("n"))), Close, Sp, Land, Sp,
                    Call("Not", Call("Nonempty", Call("AddEquiv", R("C", D(1)), R("D", D(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An additive isomorphism would preserve multiplication by 2k. "
                    + "This contradicts the constructed witness and universal annihilator. "
                    + "The predecessor supplies equality of all positive-time cardinalities. "
                    + "This theorem classifies and separates this explicit family; "
                    + "it does not prove that one-step abelian groups classify arbitrary toral automorphisms."))),
                DescribeRole.Theorem))));

    private static Formula R(string matrix, Formula time) => Call("R", F.Id(matrix), time);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) pieces.AddRange([Comma, Sp]);
            pieces.Add(arguments[i]);
        }
        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}

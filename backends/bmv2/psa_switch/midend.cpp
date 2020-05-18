/*
Copyright 2013-present Barefoot Networks, Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include "midend.h"
#include "frontends/common/constantFolding.h"
#include "frontends/common/resolveReferences/resolveReferences.h"
#include "frontends/p4/evaluator/evaluator.h"
#include "frontends/p4/fromv1.0/v1model.h"
#include "frontends/p4/moveDeclarations.h"
#include "frontends/p4/simplify.h"
#include "frontends/p4/simplifyParsers.h"
#include "frontends/p4/strengthReduction.h"
#include "frontends/p4/typeChecking/typeChecker.h"
#include "frontends/p4/typeMap.h"
#include "frontends/p4/uniqueNames.h"
#include "frontends/p4/unusedDeclarations.h"
#include "midend/actionSynthesis.h"
#include "midend/complexComparison.h"
#include "midend/convertEnums.h"
#include "midend/copyStructures.h"
#include "midend/eliminateTuples.h"
#include "midend/eliminateNewtype.h"
#include "midend/eliminateSerEnums.h"
#include "midend/flattenHeaders.h"
#include "midend/flattenInterfaceStructs.h"
#include "midend/replaceSelectRange.h"
#include "midend/local_copyprop.h"
#include "midend/nestedStructs.h"
#include "midend/removeLeftSlices.h"
#include "midend/removeMiss.h"
#include "midend/removeParameters.h"
#include "midend/removeUnusedParameters.h"
#include "midend/simplifyKey.h"
#include "midend/simplifySelectCases.h"
#include "midend/simplifySelectList.h"
#include "midend/removeSelectBooleans.h"
#include "midend/validateProperties.h"
#include "midend/compileTimeOps.h"
#include "midend/orderArguments.h"
#include "midend/predication.h"
#include "midend/expandLookahead.h"
#include "midend/expandEmit.h"
#include "midend/tableHit.h"
#include "midend/midEndLast.h"
#include "midend/fillEnumMap.h"
#include "midend/removeAssertAssume.h"
#include "backends/bmv2/psa_switch/options.h"
#include "frontends/p4/methodInstance.h"

namespace P4 {

class FixRegisterRead : public Transform {

    ReferenceMap* refMap;
    TypeMap*      typeMap;
    
    public:
        FixRegisterRead(ReferenceMap* refMap, TypeMap* typeMap):
            refMap(refMap), typeMap(typeMap)
        {CHECK_NULL(refMap); CHECK_NULL(typeMap); setName("FixRegisterRead");}

    const IR::Node *preorder(IR::AssignmentStatement *as) override {
        // locate register_read()
        auto mce = as->right->to<IR::MethodCallExpression>();
        if (mce == nullptr)
            return as;
        auto mi = P4::MethodInstance::resolve(mce, refMap, typeMap); 
        auto em = mi->to<P4::ExternMethod>();
        if (em == nullptr)
            return as;
        if (em->originalExternType->name.name != "Register" || 
                em->method->name.name != "read")
            return as;

        // build vector
        auto result = new IR::IndexedVector<IR::StatOrDecl>();
        // declaration
        auto tmp = refMap->newName("regReadTmp");
        auto type = typeMap->getType(as->left);
        // TODO need to check return value?
        auto decl = new IR::Declaration_Variable(IR::ID(tmp), type->getP4Type(), nullptr);
        result->push_back(decl);

        // register_read()
        auto regReadTmp = new IR::PathExpression(tmp);
        auto arg = new IR::Argument(regReadTmp);
        typeMap->setType(arg->expression, type);
        auto args = new IR::Vector<IR::Argument>();
        args->push_back(arg);
        args->push_back(mce->arguments->at(0));
        auto mce2 = new IR::MethodCallExpression(mce->method);
        mce2->arguments = args;
        auto mc = new IR::MethodCallStatement(mce2); 
        result->push_back(mc);

        // assignment
        result->push_back(new IR::AssignmentStatement(as->left, regReadTmp));

        // update typeMap
        auto argsInfo = new IR::Vector<IR::ArgumentInfo>();
        //auto typeArgs = new IR::Vector<IR::Type>();
        for (auto aarg : *mce2->arguments) {
            auto arg = aarg->expression;
            auto argType = typeMap->getType(arg);
            if (argType == nullptr)
                // TODO errormsg
                return nullptr;
            // std::cout << "type = " << argType << std::endl;
            auto argInfo = new IR::ArgumentInfo(arg->srcInfo, typeMap->isLeftValue(arg), typeMap->isCompileTimeConstant(arg), argType, aarg->name);
            argsInfo->push_back(argInfo);
        }
        auto retType = new IR::Type_Var(IR::ID(refMap->newName("R"), "return type"));
        auto typeArgs = new IR::Vector<IR::Type>();
        auto callType = new IR::Type_MethodCall(mce2->srcInfo, typeArgs, retType, argsInfo);
        typeMap->setType(mce2, callType);

        // update typeMap to resolve future MethodInstance()
        auto mem = mce2->method->to<IR::Member>();
        auto pe = mem->expr->to<IR::PathExpression>();
        const IR::IDeclaration *d = nullptr;
        const IR::Type *t = nullptr;
        d = refMap->getDeclaration(pe->path, true);
        t = typeMap->getType(d->getNode());
        t = t->to<IR::Type_SpecializedCanonical>()->substituted->to<IR::Type>();
        auto et = t->to<IR::Type_Extern>();
        auto methods2 = new IR::Vector<IR::Method>();
        for (auto m : et->methods) {
            methods2->push_back(m);
            methods2->push_back(m);
        }
        auto et2 = new IR::Type_Extern(et->srcInfo, et->name, et->typeParameters, *methods2);
        auto t2 = et2->to<IR::Type_SpecializedCanonical>();
        typeMap->setType(d->getNode(), t2);
        // test
        const IR::IDeclaration *d3 = nullptr;
        const IR::Type *t3 = nullptr;
        d3 = refMap->getDeclaration(pe->path, true);
        t3 = typeMap->getType(d3->getNode());
        t3 = t3->to<IR::Type_SpecializedCanonical>()->substituted->to<IR::Type>();
        auto et3 = t3->to<IR::Type_Extern>();
        // test end
        return result;
    }
};

}

namespace BMV2 {

/**
This class implements a policy suitable for the ConvertEnums pass.
The policy is: convert all enums that are not part of the psa.
Use 32-bit values for all enums.
Also convert PSA_PacketPath_t to bit<32>
*/
class PsaEnumOn32Bits : public P4::ChooseEnumRepresentation {
    cstring filename;

    bool convert(const IR::Type_Enum* type) const override {
        if (type->name == "PSA_PacketPath_t")
            return true;
        if (type->srcInfo.isValid()) {
            auto sourceFile = type->srcInfo.getSourceFile();
            if (sourceFile.endsWith(filename))
                // Don't convert any of the standard enums
                return false;
        }
        return true;
    }
    unsigned enumSize(unsigned) const override
    { return 32; }

 public:
    explicit PsaEnumOn32Bits(cstring filename) : filename(filename) { }
};

PsaSwitchMidEnd::PsaSwitchMidEnd(CompilerOptions& options, std::ostream* outStream)
                                : MidEnd(options) {
    auto convertEnums = new P4::ConvertEnums(&refMap, &typeMap, new PsaEnumOn32Bits("psa.p4"));
    auto evaluator = new P4::EvaluatorPass(&refMap, &typeMap);
    if (BMV2::PsaSwitchContext::get().options().loadIRFromJson == false) {
        std::initializer_list<Visitor *> midendPasses = {
            options.ndebug ? new P4::RemoveAssertAssume(&refMap, &typeMap) : nullptr,
            new P4::RemoveMiss(&refMap, &typeMap),
            new P4::EliminateNewtype(&refMap, &typeMap),
            new P4::EliminateSerEnums(&refMap, &typeMap),
            new P4::RemoveActionParameters(&refMap, &typeMap),
            convertEnums,
            new VisitFunctor([this, convertEnums]() { enumMap = convertEnums->getEnumMapping(); }),
            new P4::OrderArguments(&refMap, &typeMap),
            new P4::TypeChecking(&refMap, &typeMap),
            new P4::SimplifyKey(&refMap, &typeMap,
                                new P4::OrPolicy(
                                    new P4::IsValid(&refMap, &typeMap),
                                    new P4::IsMask())),
            new P4::ConstantFolding(&refMap, &typeMap),
            new P4::StrengthReduction(&refMap, &typeMap),
            new P4::SimplifySelectCases(&refMap, &typeMap, true),  // require constant keysets
            new P4::ExpandLookahead(&refMap, &typeMap),
            new P4::ExpandEmit(&refMap, &typeMap),
            new P4::SimplifyParsers(&refMap),
            new P4::StrengthReduction(&refMap, &typeMap),
            new P4::EliminateTuples(&refMap, &typeMap),
            new P4::SimplifyComparisons(&refMap, &typeMap),
            new P4::CopyStructures(&refMap, &typeMap),
            new P4::NestedStructs(&refMap, &typeMap),
            new P4::SimplifySelectList(&refMap, &typeMap),
            new P4::RemoveSelectBooleans(&refMap, &typeMap),
            new P4::FlattenHeaders(&refMap, &typeMap),
            new P4::FlattenInterfaceStructs(&refMap, &typeMap),
            new P4::ReplaceSelectRange(&refMap, &typeMap),
            new P4::FixRegisterRead(&refMap, &typeMap),
            new P4::TypeChecking(&refMap, &typeMap),
            new P4::Predication(&refMap),
            new P4::MoveDeclarations(),  // more may have been introduced
            new P4::ConstantFolding(&refMap, &typeMap),
            new P4::LocalCopyPropagation(&refMap, &typeMap),
            new P4::ConstantFolding(&refMap, &typeMap),
            new P4::MoveDeclarations(),
            new P4::ValidateTableProperties({ "psa_implementation",
                                              "psa_direct_counter",
                                              "psa_direct_meter",
                                              "psa_idle_timeout",
                                              "size" }),
            new P4::SimplifyControlFlow(&refMap, &typeMap),
            new P4::CompileTimeOperations(),
            new P4::TableHit(&refMap, &typeMap),
            new P4::MoveActionsToTables(&refMap, &typeMap),
            new P4::RemoveLeftSlices(&refMap, &typeMap),
            new P4::TypeChecking(&refMap, &typeMap),
            new P4::MidEndLast(),
            evaluator,
            new VisitFunctor([this, evaluator]() { toplevel = evaluator->getToplevelBlock(); }),
        };
        if (options.listMidendPasses) {
            for (auto it : midendPasses) {
                if (it != nullptr) {
                    *outStream << it->name() <<'\n';
                }
            }
            return;
        }
        addPasses(midendPasses);
        if (options.excludeMidendPasses) {
            removePasses(options.passesToExcludeMidend);
        }
    } else {
        auto fillEnumMap = new P4::FillEnumMap(new PsaEnumOn32Bits("psa.p4"), &typeMap);
        addPasses({
            new P4::ResolveReferences(&refMap),
            new P4::TypeChecking(&refMap, &typeMap),
            fillEnumMap,
            new VisitFunctor([this, fillEnumMap]() { enumMap = fillEnumMap->repr; }),
            evaluator,
            new VisitFunctor([this, evaluator]() { toplevel = evaluator->getToplevelBlock(); }),
        });
    }
}

}  // namespace BMV2

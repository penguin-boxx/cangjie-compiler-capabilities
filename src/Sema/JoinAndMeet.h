// Copyright (c) Huawei Technologies Co., Ltd. 2025. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
//
// See https://cangjie-lang.cn/pages/LICENSE for license information.

/**
 * @file
 *
 * This file declares the class for calculating the smallest common supertype (or join, or least upper bound) and the
 * greatest common subtype (or meet, or greatest lower bound) of the given set of types.
 */
#ifndef CANGJIE_SEMA_JOINANDMEET_H
#define CANGJIE_SEMA_JOINANDMEET_H

#include <functional>
#include <variant>

#include "cangjie/AST/Types.h"
#include "cangjie/Modules/ImportManager.h"
#include "cangjie/Sema/TypeManager.h"

namespace Cangjie {
struct DualMode {
    Ptr<AST::Ty> bound;                                                    // Any for join, Nothing for meet
    std::function<Ptr<AST::Ty>(const std::set<Ptr<AST::Ty>>&)> coFunc;     // join for join, meet for meet
    std::function<Ptr<AST::Ty>(const std::set<Ptr<AST::Ty>>&)> contraFunc; // meet for join, join for meet
    std::function<bool(Ptr<AST::Ty>, Ptr<AST::Ty>)> coSubtyFunc;           // is-subtype for join, is-supertype for meet
    bool isJoin{true}; // true for join, false for meet (capability lists combine asymmetrically)
};

class JoinAndMeet {
    using ErrMsg = std::stack<std::string>;
    using ErrOrTy = std::variant<ErrMsg, Ptr<AST::Ty>>;

public:
    // if curFile is given, impMgr must also be given
    JoinAndMeet(TypeManager& tyMgr, const std::initializer_list<Ptr<AST::Ty>> tySet,
        const std::initializer_list<Ptr<TyVar>> ignoredTyVars = {}, Ptr<const ImportManager> impMgr = nullptr,
        Ptr<AST::File> curFile = nullptr)
        : tyMgr(tyMgr), tySet(tySet), ignoredTyVars(ignoredTyVars), impMgr(impMgr), curFile(curFile)
    {
    }
    // if curFile is given, impMgr must also be given
    JoinAndMeet(TypeManager& tyMgr, const std::set<Ptr<AST::Ty>> tySet, const std::set<Ptr<TyVar>> ignoredTyVars = {},
        Ptr<const ImportManager> impMgr = nullptr, Ptr<AST::File> curFile = nullptr)
        : tyMgr(tyMgr), tySet(tySet), ignoredTyVars(ignoredTyVars), impMgr(impMgr), curFile(curFile)
    {
    }

    /**
     * Calculate the join (i.e. least upper bound) of two types.
     * sprsErr: suppress error messages. We opt in reporting the summary of errors after the join (meet) finishes and
     * the error messages produced along the calculation are regarded as logs for debuging.
     * Turn the sprsErr from true to false when debuging this module.
     */
    ErrOrTy Join(bool sprsErr = true);
    ErrOrTy JoinAsVisibleTy();
    /**
     * Calculate the meet (i.e. greatest lower bound) of two types.
     */
    ErrOrTy Meet(bool sprsErr = true);
    ErrOrTy MeetAsVisibleTy();
    static std::string CombineErrMsg(ErrMsg& msgs);

    static std::pair<std::optional<std::string>, Ptr<AST::Ty>> SetJoinedType(
        Ptr<AST::Ty> ty, std::variant<std::stack<std::string>, Ptr<AST::Ty>>& joinRes);
    static std::pair<std::optional<std::string>, Ptr<AST::Ty>> SetMetType(
        Ptr<AST::Ty> ty, std::variant<std::stack<std::string>, Ptr<AST::Ty>>& metRes);

    // Convert the input type to a user-visible one by eliminating intersection and union types.
    // Use a boolean value isJoin to distinguish the join and meet mode.
    Ptr<AST::Ty> ToUserVisibleTy(Ptr<AST::Ty> ty);

private:
    TypeManager& tyMgr;
    const std::set<Ptr<AST::Ty>> tySet;
    const TyVars ignoredTyVars;
    Ptr<const ImportManager> impMgr;
    Ptr<AST::File> curFile;
    ErrMsg errMsg;
    bool isForcedToUserVisible = false;

    Ptr<AST::Ty> BatchJoin(const std::set<Ptr<AST::Ty>>& tys);
    Ptr<AST::Ty> BatchMeet(const std::set<Ptr<AST::Ty>>& tys);

    Ptr<AST::Ty> JoinOrMeetFuncTy(const DualMode& mode, const std::set<Ptr<AST::Ty>>& tys);
    // Checked exceptions: union of capability lists for join, entries covered by all lists for meet.
    std::vector<Ptr<AST::Ty>> JoinOrMeetCapTys(const DualMode& mode, const std::set<Ptr<AST::Ty>>& tys);
    Ptr<AST::Ty> JoinOrMeetTupleTy(const DualMode& mode, const std::set<Ptr<AST::Ty>>& tys);

    void AddFinalErrMsgs(const AST::Ty& ty, bool isJoin);
    bool IsInputValid() const;
};
} // namespace Cangjie
#endif // CANGJIE_SEMA_JOINANDMEET_H

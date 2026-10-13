// Copyright (c) Huawei Technologies Co., Ltd. 2026. All rights reserved.
// This source file is part of the Cangjie project, licensed under Apache-2.0
// with Runtime Library Exception.
#ifndef CANGJIE_MODULES_CAPABILITYCACHE_H
#define CANGJIE_MODULES_CAPABILITYCACHE_H
#include <string>
#include <vector>
namespace Cangjie {
class GlobalOptions;
class ImportManager;
/// Original dependency policies and capability signatures, independent of consumer projection.
std::vector<std::string> CapabilityCacheKey(const GlobalOptions& options, const ImportManager& imports);
} // namespace Cangjie
#endif

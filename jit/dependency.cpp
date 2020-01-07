#include <cassert>

#include "dependency.h"
namespace RGDPROXY {

  DependencyNode::DependencyNode()
    : dependencies_(NULL)
  {}

  DependencyNode::~DependencyNode() {
    delete dependencies_;
  }

  DependencySet* DependencyNode::getDependencies() {
    if (dependencies_ == NULL)
      dependencies_ = new DependencySet(computeDependencies());
    return dependencies_;
  }
}
